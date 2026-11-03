import CRNT.Dynamics.ConservationLaw
import CRNT.Stoich.ConservationDimension
import CRNT.Open.Augmentation
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Conservation laws of an open system with a constant inflow

An *open* system exchanges material with its surroundings.  Here the exchange is modelled
by a **constant inflow** `f : S → ℝ`: species `s` is produced at the constant rate `f s`,
the pseudo-reaction `0 → s`.  The dynamics of the opened network `G_f` is the mass-action
field of `G` plus the constant inflow.

## The classical result

For a network `G` opened with the constant inflow `f`, the conservation laws of the opened
network are exactly

```
L(G_f) = L(G) ∩ f^⊥,
```

that is, the conservation laws of the closed network which are in addition orthogonal to the
inflow.  This is the conservation-law theory of open systems of T. Mizoguchi, *The
conservation laws in open chemical reaction networks* (2020), and it is the linear part of
the CFSTR (continuous-flow stirred-tank reactor) framework of M. Feinberg, *Foundations of
Chemical Reaction Network Theory* (Springer, 2019), Ch. 10.

## What the repository already had

* `CRNT/Stoich/ConservationDimension.lean`: the conservation-law *space* of a closed network
  (`Network.conservationLawSpace`) and its dimension (`finrank_conservationLawSpace`);
* `CRNT/Dynamics/ConservationLaw.lean`: the *constant-of-motion* theorem for closed
  networks (`Network.conservationLaw_const_along_solution`);
* `CRNT/Open/Augmentation.lean`: the **uniform** inflow case, in which the open system is
  the fully open extension (`0 → s` and `s → 0` for every species); its stoichiometric
  subspace is the whole species space and it has no conservation law at all
  (`orthSum_stoichSubspace_fullyOpen_eq_bot`).

## What this module adds: the general inflow theory

For an *arbitrary* constant inflow `f`:

* `openMassActionVectorField`: the open mass-action field `ẋ = f_massaction(x) + f`;
* `openStoichSubspace`: the open stoichiometric subspace `S(G) + span{f}`;
* `open_conservationLawSpace`: the classification `L(G_f) = L(G) ∩ f^⊥`, i.e.
  `orthSum (openStoichSubspace f) = conservationLawSpace ⊓ orthSum (span {f})`, together
  with the classical formulation `mem_orthSum_openStoichSubspace_iff` ("orthogonal to every
  reaction vector *and* to the inflow") and with the Euclidean form
  `open_conservationLawSpace_orthogonal`, which uses Mathlib's `Submodule.orthogonal`;
* `open_weightedTotal_const_along_solution`: the dynamic half — a conservation law of the
  open system is a constant of motion along every open solution;
* `finrank_openConservationLawSpace`: the dimension — opening the network lowers the
  dimension of the conservation-law space by the rank of the inflow pairing
  `w ↦ ∑ s, w s · f s`.

(The dot-product orthogonal complement of `CRNT/LinearAlgebra/OrthogonalComplement.lean` is
written `orthSum`; Mathlib's `Submodule.orthogonal` is only available on the Euclidean
space `EuclideanSpace ℝ S`, so the statements below use `orthSum`, and
`open_conservationLawSpace_orthogonal` transports them to `Submodule.orthogonal`.)

## A caveat: the "strictly positive inflow" corollary

The often-suggested corollary *"a strictly positive inflow leaves no conservation law"* is
**false**: `not_open_conservationLaw_eq_bot_of_pos` exhibits a counterexample — the network
`A → B`, `C → D` opened with the strictly positive inflow `(1,1,1,1)` still carries the
nonzero conservation law `(1,1,−1,−1)`, which is orthogonal to both reaction vectors and to
the inflow.  What *is* true is the nonnegative (P-semiflow) version
`open_conservationLaw_nonneg_eq_bot`: a strictly positive inflow leaves no nonzero
*nonnegative* conservation law.  `open_conservationLaw_eq_bot_iff` gives the exact
criterion for the open conservation-law space to be trivial.

## Not formalized here

The *dynamical* theory of open systems — the CFSTR itself (the augmented network with
inflow and outflow pseudo-reactions, its boundary equilibria, its attractor) — is **not**
formalized in this module; `CRNT/Open/Augmentation.lean`, `CRNT/Open/Boundary.lean`,
`CRNT/Open/PartialOpen.lean` and `CRNT/Open/Deficiency*.lean` cover the augmented-network
side.  Here the inflow is a *constant vector* added to the mass-action field, and only the
linear (conservation-law) theory is developed.

Depends on: `CRNT.Dynamics.ConservationLaw`, `CRNT.Stoich.ConservationDimension`,
`CRNT.Open.Augmentation`, `CRNT.LinearAlgebra.OrthogonalComplement`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The open mass-action field.**  The dynamics of the network `G` opened with the constant
inflow `f` is the mass-action field plus the constant inflow: species `s` is produced at the
constant rate `f s` (the pseudo-reaction `0 → s`). -/
def openMassActionVectorField (N : Network S) (κ : N.RateConstants) (f : S → ℝ)
    (x : Concentration S) : Concentration S :=
  N.massActionVectorField κ x + f

@[simp] theorem openMassActionVectorField_apply (N : Network S) (κ : N.RateConstants)
    (f : S → ℝ) (x : Concentration S) (s : S) :
    N.openMassActionVectorField κ f x s = N.massActionVectorField κ x s + f s := by
  rw [openMassActionVectorField, Pi.add_apply]

/-- **The stoichiometric subspace of the opened network.**  The span of the reaction vectors
of `G` together with the inflow direction `f`; its orthogonal complement is the conservation-
law space of the opened network. -/
def openStoichSubspace (N : Network S) (f : S → ℝ) : Submodule ℝ (S → ℝ) :=
  N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ))

omit [DecidableEq S] in
/-- The orthogonal complement of a sum is the intersection of the orthogonal complements:
`(A ⊔ B)ᗮ = Aᗮ ∩ Bᗮ`. -/
theorem orthSum_sup (A B : Submodule ℝ (S → ℝ)) :
    orthSum (A ⊔ B) = orthSum A ⊓ orthSum B := by
  ext w
  constructor
  · intro h
    have hA : A ≤ A ⊔ B := le_sup_left
    have hB : B ≤ A ⊔ B := le_sup_right
    refine ⟨mem_orthSum.mpr (fun a ha => h a (hA ha)),
      mem_orthSum.mpr (fun b hb => h b (hB hb))⟩
  · intro h v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have ha' : (∑ i, w i * a i) = 0 := (mem_orthSum.mp h.1) a ha
    have hb' : (∑ i, w i * b i) = 0 := (mem_orthSum.mp h.2) b hb
    have hsplit : (∑ i, w i * (a + b) i) = (∑ i, w i * a i) + (∑ i, w i * b i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply]; ring
    rw [hsplit, ha', hb', add_zero]

/-- **The conservation laws of an open system.**  A vector is a conservation law of the
opened network `G_f` exactly when it is a conservation law of the closed network `G` *and* it
is orthogonal to the inflow: `L(G_f) = L(G) ∩ f^⊥`. -/
theorem open_conservationLawSpace (N : Network S) (f : S → ℝ) :
    orthSum (N.openStoichSubspace f) = N.conservationLawSpace ⊓ orthSum (Submodule.span ℝ {f}) := by
  have h1 : N.conservationLawSpace = orthSum N.stoichSubspace := rfl
  have h2 : N.openStoichSubspace f = N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ)) := rfl
  rw [h1, h2, orthSum_sup]

/-- **The conservation laws of an open system, in Euclidean form.**  This is the same
statement as `open_conservationLawSpace`, transported to the Euclidean space
`EuclideanSpace ℝ S` where Mathlib's `Submodule.orthogonal` is available (the dot-product
orthogonal complement `orthSum` of `CRNT/LinearAlgebra/OrthogonalComplement.lean` is by
definition this orthogonal complement). -/
theorem open_conservationLawSpace_orthogonal (N : Network S) (f : S → ℝ) :
    ((N.openStoichSubspace f).map toEuclid.toLinearMap).orthogonal
      = (N.stoichSubspace.map toEuclid.toLinearMap).orthogonal
        ⊓ ((Submodule.span ℝ ({f} : Set (S → ℝ))).map toEuclid.toLinearMap).orthogonal := by
  have hinj : Function.Injective (toEuclid.toLinearMap : (S → ℝ) →ₗ[ℝ] _) :=
    toEuclid.injective
  have hmap (K : Submodule ℝ (S → ℝ)) :
      (orthSum K).map toEuclid.toLinearMap = (K.map toEuclid.toLinearMap).orthogonal := by
    rw [orthSum_eq]
    exact Submodule.map_comap_eq_of_surjective toEuclid.surjective
      (K.map toEuclid.toLinearMap).orthogonal
  rw [← hmap (N.openStoichSubspace f), ← hmap N.stoichSubspace,
    ← hmap (Submodule.span ℝ ({f} : Set (S → ℝ)))]
  have h2 : orthSum N.stoichSubspace ⊓ orthSum (Submodule.span ℝ ({f} : Set (S → ℝ)))
      = orthSum (N.openStoichSubspace f) := by
    unfold Network.openStoichSubspace
    exact (N.open_conservationLawSpace f).symm
  rw [← Submodule.map_inf _ hinj, h2]

/-- **The classical form of the open conservation laws.**  A vector is a conservation law of
the opened network exactly when it is orthogonal to every reaction vector of the closed
network *and* orthogonal to the inflow. -/
theorem mem_orthSum_openStoichSubspace_iff (N : Network S) (f : S → ℝ) {w : S → ℝ} :
    w ∈ orthSum (N.openStoichSubspace f) ↔
      (∀ r : N.R, (∑ i, w i * N.reactionVector r i) = 0) ∧ ((∑ i, w i * f i) = 0) := by
  have hA_le : N.stoichSubspace ≤ N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ)) :=
    le_sup_left
  have hB_le : Submodule.span ℝ ({f} : Set (S → ℝ))
      ≤ N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ)) := le_sup_right
  constructor
  · intro hw
    refine ⟨fun r => (mem_orthSum.mp hw) _ (hA_le (N.reactionVector_mem_stoichSubspace r)),
      (mem_orthSum.mp hw) f (hB_le (Submodule.subset_span (Set.mem_singleton f)))⟩
  · intro hw
    have hA : w ∈ orthSum N.stoichSubspace := by
      simp only [Network.stoichSubspace]
      apply mem_orthSum_span
      rintro g ⟨r, rfl⟩
      exact hw.1 r
    have hB : w ∈ orthSum (Submodule.span ℝ ({f} : Set (S → ℝ))) := by
      apply mem_orthSum_span
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hw.2
    unfold Network.openStoichSubspace
    rw [orthSum_sup]
    exact ⟨hA, hB⟩

/-- **The derivative of the weighted total along an open solution.** -/
theorem hasDerivAt_openWeightedTotal (N : Network S) (κ : N.RateConstants) (f : S → ℝ)
    (w : S → ℝ) {γ : ℝ → Concentration S} {t : ℝ}
    (hsol : HasDerivAt γ (N.openMassActionVectorField κ f (γ t)) t) :
    HasDerivAt (fun τ => ∑ s, w s * γ τ s)
      (∑ s, w s * N.openMassActionVectorField κ f (γ t) s) t := by
  have hfun : (fun τ : ℝ => ∑ s, w s * γ τ s)
      = ∑ s ∈ (Finset.univ : Finset S), (fun τ : ℝ => w s * γ τ s) := by
    funext τ; rw [Finset.sum_apply]
  rw [hfun]
  exact HasDerivAt.sum (u := (Finset.univ : Finset S))
    (fun i _ => HasDerivAt.const_mul (w i) ((hasDerivAt_pi.mp hsol) i))

/-- **A conservation law of an open system is a constant of motion.**  Along every solution
of the open system `ẋ = N.openMassActionVectorField κ f x`, the weighted total
`∑ s, w s · γ(t) s` is unchanged from time `0` to time `t`, for every `w` in the open
conservation-law space.  The inflow contributes the constant `⟨w, f⟩`, which vanishes for an
open conservation law. -/
theorem open_weightedTotal_const_along_solution (N : Network S) (κ : N.RateConstants)
    (f : S → ℝ) {w : S → ℝ} (hw : w ∈ orthSum (N.openStoichSubspace f))
    {γ : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ ∈ Set.Icc (0 : ℝ) t, HasDerivAt γ (N.openMassActionVectorField κ f (γ τ)) τ) :
    ∑ s, w s * γ t s = ∑ s, w s * γ 0 s := by
  have hw' : w ∈ orthSum N.stoichSubspace ⊓ orthSum (Submodule.span ℝ ({f} : Set (S → ℝ))) := by
    have hmem : w ∈ N.conservationLawSpace ⊓ orthSum (Submodule.span ℝ ({f} : Set (S → ℝ))) :=
      (N.open_conservationLawSpace f).symm ▸ hw
    exact hmem
  have hA : w ∈ orthSum N.stoichSubspace := hw'.1
  have hB : w ∈ orthSum (Submodule.span ℝ ({f} : Set (S → ℝ))) := hw'.2
  have hp : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt (fun τ => ∑ i, w i * γ τ i) (0 : ℝ) (Set.Icc (0 : ℝ) t) τ := by
    intro τ hτ
    have hzero : (∑ i, w i * N.openMassActionVectorField κ f (γ τ) i) = 0 := by
      have h1 : (∑ i, w i * N.massActionVectorField κ (γ τ) i) = 0 :=
        (mem_orthSum.mp hA) _ (N.massActionVectorField_mem_stoichSubspace κ (γ τ))
      have h2 : (∑ i, w i * f i) = 0 :=
        (mem_orthSum.mp hB) f (Submodule.subset_span (Set.mem_singleton f))
      calc (∑ i, w i * N.openMassActionVectorField κ f (γ τ) i)
          = ∑ i, w i * (N.massActionVectorField κ (γ τ) i + f i) := by
              exact Finset.sum_congr rfl fun i _ => by rw [openMassActionVectorField_apply]
        _ = (∑ i, w i * N.massActionVectorField κ (γ τ) i) + (∑ i, w i * f i) := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun i _ => by rw [mul_add]
        _ = 0 := by rw [h1, h2, add_zero]
    have hd := N.hasDerivAt_openWeightedTotal κ f w (hsol τ hτ)
    rw [hzero] at hd
    exact hd.hasDerivWithinAt
  have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hp
    (fun τ _ => by simp) (convex_Icc 0 t) ⟨le_refl 0, ht⟩ ⟨ht, le_refl t⟩
  simp only [zero_mul] at hle
  have h0 : ‖(∑ i, w i * γ t i) - (∑ i, w i * γ 0 i)‖ = 0 := le_antisymm hle (norm_nonneg _)
  rwa [norm_eq_zero, sub_eq_zero] at h0

open Classical in
/-- **The rank of the inflow direction.**  Opening the network with the inflow `f` lowers the
dimension of the conservation-law space by one exactly when the inflow direction is *not*
already a stoichiometric direction of the closed network.  This is the rank of the inflow
pairing `w ↦ ∑ s, w s · f s` on the conservation-law space, which is the zero map exactly
when `f` is stoichiometric (`inflowPairing_eq_zero_iff`) and otherwise has rank one. -/
noncomputable def inflowRank (N : Network S) (f : S → ℝ) : ℕ :=
  if f ∈ N.stoichSubspace then 0 else 1

/-- **The inflow pairing vanishes on the conservation-law space exactly when the inflow is a
stoichiometric direction.**  This identifies `inflowRank` with the rank of the linear map
`w ↦ ∑ s, w s · f s` restricted to the conservation-law space. -/
theorem inflowPairing_eq_zero_iff (N : Network S) (f : S → ℝ) :
    (∀ w ∈ N.conservationLawSpace, (∑ i, w i * f i) = 0) ↔ f ∈ N.stoichSubspace := by
  constructor
  · intro h
    rw [← orthSum_orthSum N.stoichSubspace, mem_orthSum]
    intro w hw
    have h0 := h w hw
    have hsplit : (∑ i, f i * w i) = ∑ i, w i * f i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hsplit, h0]
  · intro hf w hw
    exact (mem_orthSum.mp hw) f hf

/-- **The dimension of the conservation-law space of an open system.**  Opening the network
with the inflow `f` reduces the dimension of the conservation-law space by the rank of the
inflow pairing `w ↦ ∑ s, w s · f s`: by one if the inflow is a new (non-stoichiometric)
direction, and by nothing if the inflow direction is already stoichiometric. -/
theorem finrank_openConservationLawSpace (N : Network S) (f : S → ℝ) :
    Module.finrank ℝ (orthSum (N.openStoichSubspace f))
      = Module.finrank ℝ N.conservationLawSpace - N.inflowRank f := by
  by_cases hf : f ∈ N.stoichSubspace
  · -- the inflow direction is already stoichiometric: the conservation laws do not change
    have hB : Submodule.span ℝ ({f} : Set (S → ℝ)) ≤ N.stoichSubspace := by
      refine Submodule.span_le.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hf
    have hsup : N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ)) = N.stoichSubspace := by
      ext v
      constructor
      · intro hv
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        have hb' : b ∈ N.stoichSubspace := hB hb
        exact N.stoichSubspace.add_mem ha hb'
      · intro hv
        have hle : N.stoichSubspace
            ≤ N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ)) := le_sup_left
        exact hle hv
    have horth : orthSum (N.openStoichSubspace f) = N.conservationLawSpace := by
      unfold Network.openStoichSubspace
      rw [hsup]
      rfl
    have hrank : N.inflowRank f = 0 := by
      simp only [Network.inflowRank]
      exact ite_eq_left hf
    rw [horth, hrank, Nat.sub_zero]
  · -- the inflow is a new direction: exactly one conservation law is lost
    have hfne : f ≠ 0 := by
      rintro rfl
      exact hf (Submodule.zero_mem N.stoichSubspace)
    have hinf : N.stoichSubspace ⊓ Submodule.span ℝ ({f} : Set (S → ℝ)) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hvA, hvB⟩ := hv
      obtain ⟨c : ℝ, hcv⟩ :=
        Submodule.mem_span_singleton.mp (show v ∈ Submodule.span ℝ (Set.singleton f) from hvB)
      rw [← hcv] at hvA ⊢
      by_cases hc : c = 0
      · rw [hc, zero_smul]
        exact Submodule.zero_mem _
      · exfalso
        apply hf
        have hcm : c⁻¹ • (c • f) ∈ N.stoichSubspace :=
          Submodule.smul_mem N.stoichSubspace c⁻¹ hvA
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hcm
        exact hcm
    have hfinB : Module.finrank ℝ (Submodule.span ℝ ({f} : Set (S → ℝ))) = 1 := by
      have hle : Module.finrank ℝ (Submodule.span ℝ ({f} : Set (S → ℝ))) ≤ 1 := by
        have h := finrank_span_le_card (M := S → ℝ) (R := ℝ) ({f} : Set (S → ℝ))
        rwa [Set.toFinset_singleton, Finset.card_singleton] at h
      have hne : Module.finrank ℝ (Submodule.span ℝ ({f} : Set (S → ℝ))) ≠ 0 := by
        intro h0
        have hbot : Submodule.span ℝ ({f} : Set (S → ℝ)) = ⊥ :=
          (Submodule.finrank_eq_zero (R := ℝ) (M := (S → ℝ))).mp h0
        have hfmem : f ∈ Submodule.span ℝ ({f} : Set (S → ℝ)) :=
          Submodule.subset_span (Set.mem_singleton f)
        rw [hbot] at hfmem
        exact hfne (by simpa using hfmem)
      omega
    have key := Submodule.finrank_sup_add_finrank_inf_eq N.stoichSubspace
      (Submodule.span ℝ ({f} : Set (S → ℝ)))
    rw [hinf, finrank_bot, add_zero] at key
    have hle : Module.finrank ℝ N.stoichSubspace + 1 ≤ Fintype.card S := by
      have h1 := Submodule.finrank_le
        (N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ)))
      rw [key, hfinB, Module.finrank_pi ℝ] at h1
      exact h1
    have hrank : N.inflowRank f = 1 := by
      simp only [Network.inflowRank]
      exact ite_eq_right hf
    rw [hrank]
    unfold Network.openStoichSubspace
    rw [finrank_orthSum, key, hfinB, N.finrank_conservationLawSpace]
    simp only [Network.stoichRank]
    omega

/-- **When is the open conservation-law space trivial?**  Opening the network removes one
conservation law (unless the inflow is already a stoichiometric direction), so the opened
network has no conservation law at all exactly when the closed network has no conservation
law at all, or when the closed network has at most one conservation law and the inflow is a
genuinely new direction. -/
theorem open_conservationLaw_eq_bot_iff (N : Network S) (f : S → ℝ) :
    orthSum (N.openStoichSubspace f) = ⊥ ↔
      (f ∈ N.stoichSubspace ∧ Module.finrank ℝ N.conservationLawSpace = 0) ∨
        (f ∉ N.stoichSubspace ∧ Module.finrank ℝ N.conservationLawSpace ≤ 1) := by
  rw [← Submodule.finrank_eq_zero (R := ℝ) (M := (S → ℝ)),
    N.finrank_openConservationLawSpace]
  generalize hn : Module.finrank ℝ N.conservationLawSpace = n
  by_cases hf : f ∈ N.stoichSubspace
  · simp only [Network.inflowRank, ite_eq_left hf, Nat.sub_zero]
    constructor
    · intro h
      exact Or.inl ⟨hf, h⟩
    · rintro (⟨hf', h⟩ | ⟨hf', h⟩)
      · exact h
      · exact absurd hf' (fun hh => hh hf)
  · simp only [Network.inflowRank, ite_eq_right hf]
    constructor
    · intro h
      exact Or.inr ⟨hf, by omega⟩
    · rintro (⟨hf', h⟩ | ⟨hf', h⟩)
      · exact absurd hf' hf
      · exact by omega

/-- **A strictly positive inflow annihilates every nonnegative conservation law.**  If the
inflow `f` is strictly positive in every species, the only *nonnegative* conservation law of
the opened network is `0`: the weighted total `∑ s, w s · f s` vanishes while every term is
nonnegative, so every `w s` vanishes. -/
theorem eq_zero_of_mem_openConservationLaw_of_nonneg (N : Network S) (f : S → ℝ)
    (hf : ∀ s, 0 < f s) {w : S → ℝ} (hw : w ∈ orthSum (N.openStoichSubspace f))
    (hwn : ∀ s, 0 ≤ w s) : w = 0 := by
  have hfmem : f ∈ N.openStoichSubspace f := by
    unfold Network.openStoichSubspace
    have hle : Submodule.span ℝ ({f} : Set (S → ℝ))
        ≤ N.stoichSubspace ⊔ Submodule.span ℝ ({f} : Set (S → ℝ)) := le_sup_right
    exact hle (Submodule.subset_span (Set.mem_singleton f))
  have hpair : (∑ i, w i * f i) = 0 := (mem_orthSum.mp hw) f hfmem
  have hterms : ∀ i, w i * f i = 0 := by
    have hnonneg : ∀ i ∈ (Finset.univ : Finset S), 0 ≤ w i * f i := by
      intro i _
      exact mul_nonneg (hwn i) (hf i).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hpair
    intro i
    exact hz i (Finset.mem_univ i)
  funext i
  rcases mul_eq_zero.mp (hterms i) with hwi | hfi
  · exact hwi
  · exact absurd hfi (ne_of_gt (hf i))

/-- **A strictly positive inflow leaves no nonzero nonnegative conservation law.**  This is
the statement that survives for an open system with a strictly positive inflow: the opened
network has no nontrivial *nonnegative* conservation law (a P-semiflow). -/
theorem open_conservationLaw_nonneg_eq_bot (N : Network S) (f : S → ℝ) (hf : ∀ s, 0 < f s) :
    {w : S → ℝ | w ∈ orthSum (N.openStoichSubspace f) ∧ (∀ s, 0 ≤ w s)} = {0} := by
  ext w
  constructor
  · intro hw
    have hw0 : w = 0 :=
      N.eq_zero_of_mem_openConservationLaw_of_nonneg f hf hw.1 hw.2
    simpa using hw0
  · intro hw
    subst hw
    exact ⟨Submodule.zero_mem _, fun _ => le_rfl⟩

/-- **A four-species network with two independent reactions**, `A → B` and `C → D`.  Its
stoichiometric subspace has rank two, so the closed network has the two independent
conservation laws `[A] + [B]` and `[C] + [D]`. -/
private def twoPairs : Network (Fin 4) where
  R := Unit ⊕ Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := Sum.elim
    (fun _ => { source := Pi.single 0 1, target := Pi.single 1 1 })
    (fun _ => { source := Pi.single 2 1, target := Pi.single 3 1 })

/-- The standard basis vector `e_j` of the species space. -/
private def stdBasis (j : S) : S → ℝ := Pi.single j (1 : ℝ)

/-- The reaction vector of `A → B` is `e_B − e_A`. -/
private theorem twoPairs_reactionVector_inl :
    twoPairs.reactionVector (Sum.inl ()) = stdBasis 1 - stdBasis 0 := by
  funext i
  simp only [Network.reactionVector, twoPairs, Sum.elim_inl, Reaction.vector_apply]
  simp [stdBasis, Pi.single_apply, Pi.sub_apply]

/-- The reaction vector of `C → D` is `e_D − e_C`. -/
private theorem twoPairs_reactionVector_inr :
    twoPairs.reactionVector (Sum.inr ()) = stdBasis 3 - stdBasis 2 := by
  funext i
  simp only [Network.reactionVector, twoPairs, Sum.elim_inr, Reaction.vector_apply]
  simp [stdBasis, Pi.single_apply, Pi.sub_apply]

/-- The dot product of `w` with the standard basis vector `e_j` is `w j`. -/
private lemma dot_single (w : S → ℝ) (j : S) :
    (∑ i, w i * (stdBasis j) i) = w j := by
  have hsplit : (∑ i, w i * (stdBasis j) i) = ∑ i, if i = j then w i else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stdBasis, Pi.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  rw [hsplit, Finset.sum_eq_single j (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- The dot product of `w` with `e_j − e_k` is `w j − w k`. -/
private lemma sum_mul_sub (w : S → ℝ) (j k : S) :
    (∑ i, w i * (stdBasis j - stdBasis k) i) = w j - w k := by
  have h : (∑ i, w i * (stdBasis j - stdBasis k) i)
      = (∑ i, w i * (stdBasis j) i) - (∑ i, w i * (stdBasis k) i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, mul_sub]
  rw [h, dot_single, dot_single]

/-- **A strictly positive inflow does *not* kill the conservation laws.**  The suggested
corollary "strictly positive inflow ⇒ the opened network has no conservation law" is
**false**: the network `A → B`, `C → D` opened with the strictly positive inflow
`f = (1,1,1,1)` still carries the nonzero conservation law `w = (1,1,−1,−1)`, which is
orthogonal to both reaction vectors and to the inflow.  What is true is the nonnegative
version, `open_conservationLaw_nonneg_eq_bot`. -/
theorem not_open_conservationLaw_eq_bot_of_pos :
    ∃ (N : Network (Fin 4)) (f : Fin 4 → ℝ),
      (∀ s, 0 < f s) ∧ orthSum (N.openStoichSubspace f) ≠ ⊥ := by
  refine ⟨twoPairs, fun _ => 1, fun s => by simp, ?_⟩
  intro hbot
  set w : Fin 4 → ℝ := fun i => if i ≤ 1 then (1 : ℝ) else -1 with hw
  have hwmem : w ∈ orthSum (twoPairs.openStoichSubspace (fun _ => 1)) := by
    rw [twoPairs.mem_orthSum_openStoichSubspace_iff]
    constructor
    · intro r
      rcases r with _ | _
      · rw [twoPairs_reactionVector_inl, sum_mul_sub]
        simp [hw]
      · rw [twoPairs_reactionVector_inr, sum_mul_sub]
        simp [hw]
    · have : (∑ i, w i * (fun _ => 1) i) = 0 := by
        simp [hw]
        norm_num [Fin.sum_univ_succ]
      exact this
  have hwne : w ≠ 0 := by
    intro hw0
    have h0 : w 0 = 0 := congrFun hw0 0
    rw [hw] at h0
    simp at h0
  have hwzero : w = 0 := by
    rw [hbot] at hwmem
    simpa using hwmem
  exact hwne hwzero

/-! ### Axiom audit (informational) -/

#print axioms CRNT.Network.open_conservationLawSpace
#print axioms CRNT.Network.open_conservationLawSpace_orthogonal
#print axioms CRNT.Network.mem_orthSum_openStoichSubspace_iff
#print axioms CRNT.Network.open_weightedTotal_const_along_solution
#print axioms CRNT.Network.finrank_openConservationLawSpace
#print axioms CRNT.Network.open_conservationLaw_eq_bot_iff
#print axioms CRNT.Network.eq_zero_of_mem_openConservationLaw_of_nonneg
#print axioms CRNT.Network.open_conservationLaw_nonneg_eq_bot
#print axioms CRNT.Network.not_open_conservationLaw_eq_bot_of_pos
#print axioms CRNT.Network.inflowPairing_eq_zero_iff

end Network
end CRNT
