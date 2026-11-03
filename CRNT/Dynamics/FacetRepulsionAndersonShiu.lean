import CRNT.Flux.PSemiflow
import CRNT.Dynamics.LaSalle
import CRNT.Graph.CycleCover
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Dynamics.OmegaLimit
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences

open Filter
open scoped NNReal Topology

/-!
# Anderson–Shiu facet repulsion: a conditional estimate

Formalization of the one-sign argument and conditional algebraic assembly from Theorem 3.2 of
Anderson & Shiu, *The dynamics of weakly reversible population processes near facets* (SIAM J.
Appl. Math. 70 (2010), 1840–1858; arXiv:0903.0901). Given a facet direction, a nonnegative reaction
contribution, and the quantitative monomial-domination bounds, `facet_repelling_of_data` proves the
near-facet repulsion inequality.

Setting of that theorem.  `W` is a set of species whose face `F_W` is a *facet* of a positive
compatibility class `P`.  Facet-ness makes `Z_W ∩ S` have dimension `dim S - 1`, so the projection
of the stoichiometric subspace onto the `W`-coordinates is one-dimensional, spanned by `v|_W` for
some `v ∈ S`.  The proof then argues in three stages:

1. `v|_W` has all coordinates of one sign;
2. within a weakly reversible reaction component containing a negative reaction, a return path
   supplies an increasing reaction whose source is strictly smaller on `W` than that negative
   reaction's source;
3. near a facet-interior point, quantitative bounds on complementary coordinates make the
   increasing reaction's monomial dominate, forcing `∑_{i ∈ W} x_i f_i(x) ≥ 0`.

The one-sign conclusion follows from a conservation-law obstruction: if `v|_W` had a negative
coordinate `i` and a positive coordinate `j`, then `v j • e i - v i • e j` would be a nonnegative
nonzero conservation law supported inside `W`, which cannot vanish on a face reachable from a
positive point. The module also proves the facet-direction rank reduction and the monomial and sum
estimates under explicit hypotheses. The local near-facet theorem now derives the complementary
monomial bounds, finite coefficient constant, and small radius from finiteness; its end-to-end
facet wrapper derives the signed direction from a codimension-one projection-rank condition and a
compatible positive point. Identifying such a coordinate facet in the general critical-siphon
boundary branch, and converting local repulsion into the required omega-limit contradiction, remain
separate steps.

`exists_mem_speciesSupport_ne_zero_of_pSemiflow` is that obstruction in general form; it is the
quantitative content behind `Geometry/CompatibilityFaces.lean`'s face-emptiness results, but stated
for a conservation law whose support is merely *contained* in the face rather than equal to it,
which is what stage 1 needs.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A nonnegative conservation law cannot vanish on a face reachable from a positive point.**
If `w` is a nonnegative, nonzero P-invariant and `z` is a nonnegative point stoichiometrically
compatible with a strictly positive `x₀`, then `z` is nonzero somewhere on the support of `w`. -/
theorem exists_mem_speciesSupport_ne_zero_of_pSemiflow
    (N : Network S) {w : S → ℝ} (hw : N.IsPInvariant w) (hnn : ∀ s, 0 ≤ w s) (hne : w ≠ 0)
    {x₀ z : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ z) (hznn : z.Nonnegative) :
    ∃ s, w s ≠ 0 ∧ z s ≠ 0 := by
  classical
  -- the weighted total is positive at `x₀`
  obtain ⟨s₀, hs₀⟩ : ∃ s, w s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hs₀pos : 0 < w s₀ := lt_of_le_of_ne (hnn s₀) (Ne.symm hs₀)
  have hx₀pos : 0 < weightedTotal w x₀ := by
    refine Finset.sum_pos' (fun s _ => mul_nonneg (hnn s) (hx₀ s).le) ?_
    exact ⟨s₀, Finset.mem_univ s₀, mul_pos hs₀pos (hx₀ s₀)⟩
  -- it is unchanged at `z`
  have heq : weightedTotal w x₀ = weightedTotal w z :=
    N.weightedTotal_eq_of_stoichCompatible hw hcompat
  have hzpos : 0 < weightedTotal w z := heq ▸ hx₀pos
  -- so some term is nonzero
  by_contra hcon
  push_neg at hcon
  have hzero : weightedTotal w z = 0 := by
    unfold weightedTotal
    refine Finset.sum_eq_zero ?_
    intro s _
    by_cases hws : w s = 0
    · rw [hws, zero_mul]
    · rw [hcon s hws, mul_zero]
  rw [hzero] at hzpos
  exact lt_irrefl 0 hzpos

/-- **Stage 1 of Anderson–Shiu Theorem 3.2: the facet direction has one sign on `W`.**

Hypothesis `hspan` is the facet condition: every element of the stoichiometric subspace has its
`W`-coordinates proportional to `v`'s, which is what `dim (Z_W ∩ S) = dim S - 1` gives.  Given a
nonnegative point `z` of the face (vanishing on `W`) that is compatible with a strictly positive
`x₀`, the coordinates `v i` for `i ∈ W` cannot include both a negative and a positive value.

The witness is `u = v j • e i - v i • e j`: it is nonnegative, nonzero, supported in `W`, and a
P-invariant, because `hspan` makes `∑ s, u s * p s = v j * (c * v i) - v i * (c * v j) = 0` for
every `p` in the subspace. -/
theorem not_oppositeSign_of_facetProjection
    (N : Network S) {W : Finset S} {v : S → ℝ}
    (hspan : ∀ p ∈ N.stoichSubspace, ∃ c : ℝ, ∀ s ∈ W, p s = c * v s)
    {x₀ z : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ z) (hznn : z.Nonnegative)
    (hzW : ∀ s ∈ W, z s = 0)
    {i j : S} (hi : i ∈ W) (hj : j ∈ W) (hvi : v i < 0) (hvj : 0 < v j) :
    False := by
  classical
  have hij : i ≠ j := by
    intro h
    rw [h] at hvi
    exact absurd hvj (not_lt.mpr hvi.le)
  set u : S → ℝ := fun s => if s = i then v j else if s = j then -(v i) else 0 with hu
  have hui : u i = v j := by simp [hu]
  have huj : u j = -(v i) := by simp [hu, hij, Ne.symm hij]
  have hunn : ∀ s, 0 ≤ u s := by
    intro s
    by_cases hsi : s = i
    · subst hsi; rw [hui]; exact hvj.le
    · by_cases hsj : s = j
      · subst hsj; rw [huj]; linarith
      · simp [hu, hsi, hsj]
  have hune : u ≠ 0 := by
    intro h
    have : u i = 0 := by rw [h]; rfl
    rw [hui] at this
    exact absurd this (ne_of_gt hvj)
  have husupp : ∀ s, u s ≠ 0 → s ∈ W := by
    intro s hs
    by_cases hsi : s = i
    · exact hsi ▸ hi
    · by_cases hsj : s = j
      · exact hsj ▸ hj
      · simp [hu, hsi, hsj] at hs
  -- `u` is a conservation law
  have hupinv : N.IsPInvariant u := by
    rw [IsPInvariant, mem_orthSum]
    intro p hp
    obtain ⟨c, hc⟩ := hspan p hp
    have hsplit : ∑ s, u s * p s = u i * p i + u j * p j := by
      rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset S))]
      · rw [Finset.sum_pair hij]
      · intro s _ hs
        have hsi : s ≠ i := by
          intro h; exact hs (by simp [h])
        have hsj : s ≠ j := by
          intro h; exact hs (by simp [h])
        simp [hu, hsi, hsj]
    rw [hsplit, hui, huj, hc i hi, hc j hj]
    ring
  -- but then `z` must be nonzero somewhere on `supp u ⊆ W`, contradicting `hzW`
  obtain ⟨s, hus, hzs⟩ :=
    N.exists_mem_speciesSupport_ne_zero_of_pSemiflow hupinv hunn hune hx₀ hcompat hznn
  exact hzs (hzW s (husupp s hus))


/-- **Stage 2a of Anderson–Shiu Theorem 3.2: every reaction gains all of `W`, loses all of `W`, or
changes none of it.**  Once `v` is positive on `W` (stage 1) and the reaction's `W`-projection is
`γ • v|_W`, the sign of `γ` decides the direction uniformly across `W`.  This is the paper's
trichotomy (i)/(ii)/(iii). -/
theorem netGain_trichotomy_of_proj {W : Finset S} {v : S → ℝ} (hv : ∀ s ∈ W, 0 < v s)
    {y y' : S → ℝ} {γ : ℝ} (hdiff : ∀ s ∈ W, y' s - y s = γ * v s) :
    (∀ s ∈ W, y s ≤ y' s) ∨ (∀ s ∈ W, y' s ≤ y s) := by
  rcases le_or_gt 0 γ with hγ | hγ
  · left
    intro s hs
    have h := hdiff s hs
    have : 0 ≤ γ * v s := mul_nonneg hγ (hv s hs).le
    linarith
  · right
    intro s hs
    have h := hdiff s hs
    have : γ * v s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hγ.le (hv s hs).le
    linarith

/-- Along a directed path, a strict increase in one positive facet coordinate forces an
increasing reaction before the endpoint is reached. The returned source remains connected to the
endpoint by the suffix of the path. -/
theorem exists_positiveReaction_before_of_reaches (N : Network S)
    {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ} {s₀ : S} (hs₀ : s₀ ∈ W)
    (hv₀ : 0 < v s₀)
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    {a b : Complex S} (hab : N.Reaches a b)
    (hpot : (a s₀ : ℝ) < (b s₀ : ℝ)) :
    ∃ r : N.R, 0 < γ r ∧
      ((N.reaction r).source s₀ : ℝ) < (b s₀ : ℝ) ∧
      N.Reaches (N.reaction r).source b := by
  revert hpot
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hpot
      simp at hpot
  | @head a c hac hcd ih =>
      intro hpot
      rcases hac with ⟨r, hrs, hrt⟩
      by_cases hct : (c s₀ : ℝ) < (b s₀ : ℝ)
      · exact ih hct
      · have hba : (a s₀ : ℝ) < (c s₀ : ℝ) := by
          have hcb : (b s₀ : ℝ) ≤ (c s₀ : ℝ) := le_of_not_gt hct
          linarith
        have hdiff : (c s₀ : ℝ) - (a s₀ : ℝ) = γ r * v s₀ := by
          have h := hγ r s₀ hs₀
          rw [Network.reactionVector_apply, hrs, hrt] at h
          exact h
        have hγpos : 0 < γ r := by
          by_contra hnot
          have hγnonpos : γ r ≤ 0 := le_of_not_gt hnot
          have hmul : γ r * v s₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hγnonpos hv₀.le
          linarith
        refine ⟨r, hγpos, ?_, ?_⟩
        · rw [hrs]
          exact hpot
        · rw [hrs]
          exact (Reaches.single ⟨r, hrs, hrt⟩).trans hcd

/-- The difference of the endpoints of any reaction path is a scalar multiple of the common
facet direction on `W`. This is the path-level form of the one-dimensional projection condition. -/
theorem reaches_Wdifference_is_smul (N : Network S)
    {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ}
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    {src dst : Complex S} (hab : N.Reaches src dst) :
    ∃ α : ℝ, ∀ s ∈ W, (dst s : ℝ) - (src s : ℝ) = α * v s := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨0, fun _ _ => by simp⟩
  | @head a b habEdge _ ih =>
      rcases habEdge with ⟨r, hrs, hrt⟩
      obtain ⟨α, hα⟩ := ih
      refine ⟨γ r + α, ?_⟩
      intro s hs
      have hedge : (b s : ℝ) - (a s : ℝ) = γ r * v s := by
        have h := hγ r s hs
        rw [Network.reactionVector_apply, hrs, hrt] at h
        exact h
      calc
        (dst s : ℝ) - (a s : ℝ) =
            ((dst s : ℝ) - (b s : ℝ)) + ((b s : ℝ) - (a s : ℝ)) := by ring
        _ = α * v s + γ r * v s := by rw [hα s hs, hedge]
        _ = (γ r + α) * v s := by ring

/-- **Weak reversibility supplies a strictly smaller positive reaction for each negative one.**
If reaction `r` loses mass on every species of the facet set `W`, follow the weak-reversibility
return path from its target to its source. The path must cross the source's level in a positive
reaction. Since every path displacement is parallel to the positive facet direction, that
reaction's source is strictly below `r` on all of `W`. This supplies the exponent comparison for
the near-facet estimate once the complementary monomial factors are bounded. The witness may depend
on `r`; this handles multiple linkage classes without assuming their complex profiles are globally
ordered. -/
theorem exists_positiveReaction_below_of_negativeReaction (N : Network S)
    (hwr : N.WeaklyReversible) {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ}
    (hv : ∀ s ∈ W, 0 < v s)
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    (r : N.R) (hrγ : γ r < 0) {s₀ : S} (hs₀ : s₀ ∈ W) :
    ∃ ℓ : N.R, 0 < γ ℓ ∧
      ∀ s ∈ W, (N.reaction ℓ).source s < (N.reaction r).source s := by
  have htarget : ((N.reaction r).target s₀ : ℝ) < (N.reaction r).source s₀ := by
    have hdiff := hγ r s₀ hs₀
    rw [Network.reactionVector_apply] at hdiff
    have hprod : γ r * v s₀ < 0 := mul_neg_of_neg_of_pos hrγ (hv s₀ hs₀)
    linarith
  obtain ⟨ℓ, hℓγ, hℓsource, hℓreach⟩ :=
    N.exists_positiveReaction_before_of_reaches hs₀ (hv s₀ hs₀) hγ (hwr r) htarget
  obtain ⟨α, hα⟩ := N.reaches_Wdifference_is_smul hγ hℓreach
  have hαpos : 0 < α := by
    have hdiff : 0 <
        ((N.reaction r).source s₀ : ℝ) - ((N.reaction ℓ).source s₀ : ℝ) := by
      linarith
    by_contra hnot
    have hαnonpos : α ≤ 0 := le_of_not_gt hnot
    have hmul : α * v s₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hαnonpos (hv s₀ hs₀).le
    linarith [hα s₀ hs₀]
  refine ⟨ℓ, hℓγ, ?_⟩
  intro s hs
  have hdiff := hα s hs
  have hprod : 0 < α * v s := mul_pos hαpos (hv s hs)
  have hlt : ((N.reaction ℓ).source s : ℝ) < (N.reaction r).source s := by
    linarith
  exact_mod_cast hlt

/-- **A conditional finite minimum on `W`.** For a finite nonempty family whose `W`-profiles share
an affine coordinate along `v|_W`, the minimum of that coordinate picks out a profile below every
other one. Weakly reversible components can instead be handled locally by
`exists_positiveReaction_below_of_negativeReaction`; profiles in different components need not
share a common affine base. -/
theorem exists_minimal_on_W {ι : Type*} [Fintype ι] [Nonempty ι]
    {W : Finset S} {v : S → ℝ} (hv : ∀ s ∈ W, 0 < v s)
    (y : ι → S → ℝ) (c : ι → ℝ) (base : S → ℝ)
    (hproj : ∀ k, ∀ s ∈ W, y k s = base s + c k * v s) :
    ∃ k₀ : ι, ∀ k : ι, ∀ s ∈ W, y k₀ s ≤ y k s := by
  classical
  obtain ⟨k₀, -, hk₀⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι) c ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  refine ⟨k₀, ?_⟩
  intro k s hs
  have hle : c k₀ ≤ c k := hk₀ k (Finset.mem_univ k)
  have h0 := hproj k₀ s hs
  have h1 := hproj k s hs
  have : c k₀ * v s ≤ c k * v s :=
    mul_le_mul_of_nonneg_right hle (hv s hs).le
  linarith



/-! ### Stage 0: the facet condition, from the dimension count -/

/-- Coordinate projection onto a species subset, as a linear map. -/
def projOn (W : Finset S) : (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := fun p s => if s ∈ W then p s else 0
  map_add' := by
    intro p q
    funext s
    by_cases h : s ∈ W <;> simp [h]
  map_smul' := by
    intro c p
    funext s
    by_cases h : s ∈ W <;> simp [h]

@[simp] theorem projOn_apply (W : Finset S) (p : S → ℝ) (s : S) :
    projOn W p s = if s ∈ W then p s else 0 := rfl

/-- **Facet-ness gives a one-dimensional projection, hence a facet direction.**  If the image of a
subspace `U` under the `W`-projection is one-dimensional — which is exactly what
`dim (Z_W ∩ U) = dim U - 1` says, since `Z_W ∩ U` is the kernel of the projection restricted to
`U` — then some `v ∈ U` has the property that every element of `U` agrees with a multiple of `v` on
`W`.

This supplies the `hspan` hypothesis of `not_oppositeSign_of_facetProjection` and the `hγ`
hypothesis of `facet_repelling_of_data`, reducing Anderson–Shiu's stage-0 input to the rank
statement. -/
theorem exists_facetDirection {W : Finset S} (U : Submodule ℝ (S → ℝ))
    (h : Module.finrank ℝ (U.map (projOn W)) = 1) :
    ∃ v ∈ U, ∀ p ∈ U, ∃ c : ℝ, ∀ s ∈ W, p s = c * v s := by
  classical
  -- a one-dimensional image is spanned by any nonzero element of it
  have hne : U.map (projOn W) ≠ ⊥ := by
    intro hbot
    rw [hbot] at h
    simp at h
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hspanw : U.map (projOn W) = ℝ ∙ w :=
    eq_span_singleton_of_mem_of_finrank_eq_one h hwmem hw0
  obtain ⟨v, hvU, hvw⟩ := Submodule.mem_map.mp hwmem
  refine ⟨v, hvU, ?_⟩
  intro p hp
  have hpmem : projOn W p ∈ U.map (projOn W) := Submodule.mem_map_of_mem hp
  rw [hspanw] at hpmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hpmem
  refine ⟨c, ?_⟩
  intro s hs
  have hcs := congrFun hc s
  simp only [Pi.smul_apply, smul_eq_mul, projOn_apply, if_pos hs] at hcs
  have hwv : w s = v s := by
    rw [← hvw]
    simp [projOn_apply, if_pos hs]
  rw [hwv] at hcs
  exact hcs.symm

/-- The reaction-vector form of `exists_facetDirection`: a facet direction makes every reaction
vector a multiple of `v` on `W`, which is the `hγ` input of `facet_repelling_of_data`. -/
theorem exists_facetDirection_reactionVector (N : Network S) {W : Finset S}
    (h : Module.finrank ℝ (N.stoichSubspace.map (projOn W)) = 1) :
    ∃ v : S → ℝ, ∃ γ : N.R → ℝ, ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s := by
  classical
  obtain ⟨v, -, hspan⟩ := exists_facetDirection N.stoichSubspace h
  refine ⟨v, fun r => (hspan (N.reactionVector r)
    (N.reactionVector_mem_stoichSubspace r)).choose, ?_⟩
  intro r
  exact (hspan (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)).choose_spec


/-- **Rank–nullity turns the facet dimension count into the hypothesis of
`exists_facetDirection`.**  `LinearMap.ker ((projOn W).domRestrict U)` is `Z_W ∩ U` viewed inside
`U`; when it has codimension one in `U`, the `W`-projection of `U` is a line.  This is Anderson–Shiu's
"`Z_W ∩ S` is an `(s-1)`-dimensional subspace of `S`, therefore `π(S)` is one-dimensional". -/
theorem finrank_map_projOn_eq_one_of_facet {W : Finset S} (U : Submodule ℝ (S → ℝ))
    (hfacet : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict U)) + 1
        = Module.finrank ℝ U) :
    Module.finrank ℝ (U.map (projOn W)) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((projOn W).domRestrict U)
  rw [LinearMap.range_domRestrict] at h
  omega

/-- **Stage 0, end to end.**  From the facet dimension count alone, every reaction vector is a
multiple of a single facet direction `v` on `W` — the `hγ` input of `facet_repelling_of_data`. -/
theorem exists_facetDirection_of_facet (N : Network S) {W : Finset S}
    (hfacet : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict N.stoichSubspace)) + 1
        = Module.finrank ℝ N.stoichSubspace) :
    ∃ v : S → ℝ, ∃ γ : N.R → ℝ, ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s :=
  N.exists_facetDirection_reactionVector (finrank_map_projOn_eq_one_of_facet _ hfacet)


/-- **Stages 0 and 1 combined: a facet direction that is strictly positive on `W`.**  From the
facet dimension count, a nonnegative point `z` of the face compatible with a positive `x₀`, and the
paper's normalisation that the facet direction does not vanish on `W`, we obtain `v` and `γ` with
`v` strictly positive on `W` and every reaction vector equal to `γ r • v` there.  Those are two of
the four inputs of `facet_repelling_of_data`.

The nonvanishing hypothesis is Anderson–Shiu's own reduction: a species of `W` on which the facet
direction vanishes has constant concentration under every reaction, so it can be removed from the
system.  Sign normalisation is by replacing `(v, γ)` with `(-v, -γ)`. -/
theorem exists_facetDirection_pos_of_facet (N : Network S) {W : Finset S}
    (hfacet : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict N.stoichSubspace)) + 1
        = Module.finrank ℝ N.stoichSubspace)
    {x₀ z : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ z) (hznn : z.Nonnegative) (hzW : ∀ s ∈ W, z s = 0)
    (hnonvanish : ∀ v : S → ℝ,
      (∀ p ∈ N.stoichSubspace, ∃ c : ℝ, ∀ s ∈ W, p s = c * v s) → ∀ s ∈ W, v s ≠ 0) :
    ∃ v : S → ℝ, ∃ γ : N.R → ℝ,
      (∀ s ∈ W, 0 < v s) ∧ ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s := by
  classical
  obtain ⟨v, hvU, hspan⟩ :=
    exists_facetDirection N.stoichSubspace (finrank_map_projOn_eq_one_of_facet _ hfacet)
  have hvne : ∀ s ∈ W, v s ≠ 0 := hnonvanish v hspan
  -- no two coordinates of `v` on `W` have opposite signs
  have hnoopp : ∀ i ∈ W, ∀ j ∈ W, ¬ (v i < 0 ∧ 0 < v j) := by
    intro i hi j hj ⟨hvi, hvj⟩
    exact N.not_oppositeSign_of_facetProjection hspan hx₀ hcompat hznn hzW hi hj hvi hvj
  have hγex : ∀ r : N.R, ∃ c : ℝ, ∀ s ∈ W, N.reactionVector r s = c * v s :=
    fun r => hspan (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)
  rcases Finset.eq_empty_or_nonempty W with hW | ⟨s₀, hs₀⟩
  · exact ⟨v, fun r => (hγex r).choose, by simp [hW], by simp [hW]⟩
  · rcases lt_or_gt_of_ne (hvne s₀ hs₀) with hneg | hpos
    · -- all coordinates negative: flip the sign of `v` and `γ`
      refine ⟨fun s => -(v s), fun r => -((hγex r).choose), ?_, ?_⟩
      · intro s hs
        have hvs : v s < 0 := by
          rcases lt_or_gt_of_ne (hvne s hs) with h | h
          · exact h
          · exact absurd ⟨hneg, h⟩ (hnoopp s₀ hs₀ s hs)
        linarith
      · intro r s hs
        have := (hγex r).choose_spec s hs
        rw [this]; ring
    · refine ⟨v, fun r => (hγex r).choose, ?_, ?_⟩
      · intro s hs
        rcases lt_or_gt_of_ne (hvne s hs) with h | h
        · exact absurd ⟨h, hpos⟩ (hnoopp s hs s₀ hs₀)
        · exact h
      · intro r
        exact (hγex r).choose_spec

/-! ### Stage 3: monomial domination near the facet -/

/-- Splitting a mass-action monomial into its `W` and `Wᶜ` parts. -/
theorem massActionMonomial_split (W : Finset S) (y : Complex S) (x : Concentration S) :
    Complex.massActionMonomial y x
      = (∏ s ∈ W, x s ^ (y s)) * ∏ s ∈ Wᶜ, x s ^ (y s) := by
  rw [Complex.massActionMonomial, ← Finset.prod_mul_prod_compl W (fun s => x s ^ (y s))]

/-- **The domination estimate on `W`.**  If the exponents of `y` dominate those of `yt` on `W`,
strictly somewhere, and every `W`-coordinate of `x` is at most `ε ≤ 1`, then `y`'s `W`-monomial is
at most `ε` times `yt`'s.  This is what makes the minimal complex's monomial dominate as the
trajectory approaches the facet. -/
theorem prod_le_of_exponent_le {W : Finset S} {yt y : Complex S} {x : Concentration S} {ε : ℝ}
    (hxpos : ∀ s, 0 < x s) (hxW : ∀ s ∈ W, x s ≤ ε) (hε1 : ε ≤ 1)
    (hle : ∀ s ∈ W, yt s ≤ y s) {s₀ : S} (hs₀ : s₀ ∈ W) (hstrict : yt s₀ < y s₀) :
    ∏ s ∈ W, x s ^ (y s) ≤ ε * ∏ s ∈ W, x s ^ (yt s) := by
  classical
  have hx1 : ∀ s ∈ W, x s ≤ 1 := fun s hs => le_trans (hxW s hs) hε1
  -- factor the dominating monomial out
  have hsplit : ∏ s ∈ W, x s ^ (y s)
      = (∏ s ∈ W, x s ^ (yt s)) * ∏ s ∈ W, x s ^ (y s - yt s) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro s hs
    rw [← pow_add]
    congr 1
    have := hle s hs
    omega
  -- the leftover factor is at most `ε`
  have hrest : ∏ s ∈ W, x s ^ (y s - yt s) ≤ ε := by
    have hfac : x s₀ ^ (y s₀ - yt s₀) * ∏ s ∈ W.erase s₀, x s ^ (y s - yt s)
        = ∏ s ∈ W, x s ^ (y s - yt s) :=
      Finset.mul_prod_erase W (fun s => x s ^ (y s - yt s)) hs₀
    have hs₀le : x s₀ ^ (y s₀ - yt s₀) ≤ ε := by
      have hone : y s₀ - yt s₀ ≠ 0 := by omega
      exact le_trans (pow_le_of_le_one (hxpos s₀).le (hx1 s₀ hs₀) hone) (hxW s₀ hs₀)
    have herase : ∏ s ∈ W.erase s₀, x s ^ (y s - yt s) ≤ 1 := by
      calc ∏ s ∈ W.erase s₀, x s ^ (y s - yt s)
          ≤ ∏ _s ∈ W.erase s₀, (1 : ℝ) := by
            refine Finset.prod_le_prod₀
              (f := fun s => x s ^ (y s - yt s)) (g := fun _ => (1 : ℝ))
              (fun s _ => (pow_pos (hxpos s) _).le) ?_
            intro s hs
            exact pow_le_one₀ (hxpos s).le (hx1 s (Finset.mem_of_mem_erase hs))
        _ = 1 := by simp
    have hnnerase : 0 ≤ ∏ s ∈ W.erase s₀, x s ^ (y s - yt s) :=
      Finset.prod_nonneg fun s _ => (pow_pos (hxpos s) _).le
    have hs₀nn : 0 ≤ x s₀ ^ (y s₀ - yt s₀) := (pow_pos (hxpos s₀) _).le
    calc ∏ s ∈ W, x s ^ (y s - yt s)
        = x s₀ ^ (y s₀ - yt s₀) * ∏ s ∈ W.erase s₀, x s ^ (y s - yt s) := hfac.symm
      _ ≤ ε * 1 := by
          refine mul_le_mul hs₀le herase hnnerase ?_
          exact le_trans hs₀nn hs₀le
      _ = ε := by ring
  have hbase : 0 ≤ ∏ s ∈ W, x s ^ (yt s) :=
    Finset.prod_nonneg fun s _ => (pow_pos (hxpos s) _).le
  calc ∏ s ∈ W, x s ^ (y s)
      = (∏ s ∈ W, x s ^ (yt s)) * ∏ s ∈ W, x s ^ (y s - yt s) := hsplit
    _ ≤ (∏ s ∈ W, x s ^ (yt s)) * ε := by
        exact mul_le_mul_of_nonneg_left hrest hbase
    _ = ε * ∏ s ∈ W, x s ^ (yt s) := by ring

/-- **Stage 3, full monomial comparison.**  Near a facet-interior point the `Wᶜ`-coordinates are
bounded in `[Dmin, Dmax]` while the `W`-coordinates are at most `ε`.  Under those bounds the
monomial of a complex `y` that strictly dominates the minimal complex `yt` on `W` is smaller than
`yt`'s by the factor `ε · Dmax / Dmin`, stated multiplicatively to avoid division. -/
theorem massActionMonomial_domination {W : Finset S} {yt y : Complex S} {x : Concentration S}
    {ε Dmin Dmax : ℝ}
    (hxpos : ∀ s, 0 < x s) (hxW : ∀ s ∈ W, x s ≤ ε) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hle : ∀ s ∈ W, yt s ≤ y s) {s₀ : S} (hs₀ : s₀ ∈ W) (hstrict : yt s₀ < y s₀)
    (hDmin : 0 < Dmin) (hlo : Dmin ≤ ∏ s ∈ Wᶜ, x s ^ (yt s))
    (hhi : ∏ s ∈ Wᶜ, x s ^ (y s) ≤ Dmax) :
    Dmin * Complex.massActionMonomial y x
      ≤ ε * Dmax * Complex.massActionMonomial yt x := by
  classical
  have hWy : ∏ s ∈ W, x s ^ (y s) ≤ ε * ∏ s ∈ W, x s ^ (yt s) :=
    prod_le_of_exponent_le hxpos hxW hε1 hle hs₀ hstrict
  have hbase : 0 < ∏ s ∈ W, x s ^ (yt s) :=
    Finset.prod_pos fun s _ => pow_pos (hxpos s) _
  have hcompl : 0 < ∏ s ∈ Wᶜ, x s ^ (y s) :=
    Finset.prod_pos fun s _ => pow_pos (hxpos s) _
  rw [massActionMonomial_split W y x, massActionMonomial_split W yt x]
  have hstep1 : Dmin * ((∏ s ∈ W, x s ^ (y s)) * ∏ s ∈ Wᶜ, x s ^ (y s))
      ≤ Dmin * ((ε * ∏ s ∈ W, x s ^ (yt s)) * Dmax) := by
    refine mul_le_mul_of_nonneg_left ?_ hDmin.le
    exact mul_le_mul hWy hhi hcompl.le (by positivity)
  have hstep2 : Dmin * ((ε * ∏ s ∈ W, x s ^ (yt s)) * Dmax)
      ≤ ε * Dmax * ((∏ s ∈ W, x s ^ (yt s)) * ∏ s ∈ Wᶜ, x s ^ (yt s)) := by
    have hfac : 0 ≤ ε * Dmax * ∏ s ∈ W, x s ^ (yt s) := by
      have : 0 ≤ Dmax := le_trans hcompl.le hhi
      positivity
    have := mul_le_mul_of_nonneg_left hlo hfac
    nlinarith [this, hbase, hDmin]
  exact le_trans hstep1 hstep2



/-! ### Stage 3, choosing the radius: the bounds near a facet-interior point -/

/-- **The `W`-coordinates are small near the facet.**  If `z` vanishes on `W` and `x` is within `δ`
of `z` coordinatewise and nonnegative, then every `W`-coordinate of `x` is at most `δ`.  This is the
`ε = δ` of `prod_le_of_exponent_le`. -/
theorem le_delta_on_W {W : Finset S} {x z : Concentration S} {δ : ℝ}
    (hznn : ∀ s ∈ W, z s = 0) (hclose : ∀ s, |x s - z s| ≤ δ) :
    ∀ s ∈ W, x s ≤ δ := by
  intro s hs
  have h := hclose s
  rw [hznn s hs, sub_zero] at h
  exact le_trans (le_abs_self (x s)) h

/-- **The `Wᶜ`-monomial is bounded below, away from zero, near a facet-interior point.**  If `z` is
strictly positive off `W` and `δ` is smaller than every such coordinate, then for `x` within `δ` of
`z` the `Wᶜ`-part of any monomial is at least the corresponding product of `z s - δ`, which is
positive.  This supplies `Dmin`. -/
theorem prod_compl_lower_bound {W : Finset S} {x z : Concentration S} {δ : ℝ} (hδ : 0 < δ)
    (hzpos : ∀ s ∈ Wᶜ, 0 < z s) (hδlt : ∀ s ∈ Wᶜ, δ < z s)
    (hclose : ∀ s, |x s - z s| ≤ δ) (y : Complex S) :
    0 < ∏ s ∈ Wᶜ, (z s - δ) ^ (y s) ∧
      ∏ s ∈ Wᶜ, (z s - δ) ^ (y s) ≤ ∏ s ∈ Wᶜ, x s ^ (y s) := by
  classical
  refine ⟨Finset.prod_pos fun s hs => pow_pos (by linarith [hδlt s hs]) _, ?_⟩
  refine Finset.prod_le_prod₀ (fun s hs => (pow_pos (by linarith [hδlt s hs]) _).le) ?_
  intro s hs
  refine pow_le_pow_left₀ (by linarith [hδlt s hs]) ?_ _
  have h := hclose s
  have := abs_le.mp h
  linarith [this.1]

/-- **The `Wᶜ`-monomial is bounded above near a facet-interior point.**  Supplies `Dmax`. -/
theorem prod_compl_upper_bound {W : Finset S} {x z : Concentration S} {δ : ℝ}
    (hxnn : ∀ s, 0 ≤ x s)
    (hclose : ∀ s, |x s - z s| ≤ δ) (y : Complex S) :
    ∏ s ∈ Wᶜ, x s ^ (y s) ≤ ∏ s ∈ Wᶜ, (z s + δ) ^ (y s) := by
  classical
  refine Finset.prod_le_prod₀ (fun s _ => pow_nonneg (hxnn s) _) ?_
  intro s _
  refine pow_le_pow_left₀ (hxnn s) ?_ _
  have h := abs_le.mp (hclose s)
  linarith [h.2]

/-- On a fixed coordinate neighborhood with `δ < z_s` off the facet, finitely many reaction
monomials admit common positive lower and upper bounds on their complementary factors. The lower
constant is the minimum of the finitely many products at `z - δ`, and the upper constant is the
maximum of the products at `z + δ`. -/
theorem exists_uniform_complement_monomial_bounds
    {ι : Type*} [Fintype ι] [Nonempty ι] {W : Finset S}
    {z : Concentration S} {δ : ℝ} (hδ : 0 < δ)
    (hδlt : ∀ s ∈ Wᶜ, δ < z s)
    (y : ι → Complex S) :
    ∃ Dmin Dmax : ℝ, 0 < Dmin ∧ 0 < Dmax ∧
      (∀ x : Concentration S, (∀ s, |x s - z s| ≤ δ) → (∀ s, 0 ≤ x s) →
        ∀ i, Dmin ≤ ∏ s ∈ Wᶜ, x s ^ (y i s)) ∧
      (∀ x : Concentration S, (∀ s, |x s - z s| ≤ δ) → (∀ s, 0 ≤ x s) →
        ∀ i, ∏ s ∈ Wᶜ, x s ^ (y i s) ≤ Dmax) := by
  classical
  let lower (i : ι) : ℝ := ∏ s ∈ Wᶜ, (z s - δ) ^ (y i s)
  let upper (i : ι) : ℝ := ∏ s ∈ Wᶜ, (z s + δ) ^ (y i s)
  have hlowerPos (i : ι) : 0 < lower i := by
    simp only [lower]
    exact Finset.prod_pos fun s hs => pow_pos (by linarith [hδlt s hs]) _
  have hupperPos (i : ι) : 0 < upper i := by
    simp only [upper]
    exact Finset.prod_pos fun s hs => pow_pos (by linarith [hδlt s hs]) _
  obtain ⟨iMin, hiMin, hMin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι) lower
      ⟨Classical.choice (inferInstance : Nonempty ι), Finset.mem_univ _⟩
  obtain ⟨iMax, hiMax, hMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) upper
      ⟨Classical.choice (inferInstance : Nonempty ι), Finset.mem_univ _⟩
  refine ⟨lower iMin, upper iMax, hlowerPos iMin, hupperPos iMax, ?_, ?_⟩
  · intro x hclose hxnn i
    have hmin : lower iMin ≤ lower i := hMin i (Finset.mem_univ i)
    have hproduct : lower i ≤ ∏ s ∈ Wᶜ, x s ^ (y i s) := by
      simpa [lower] using
        (prod_compl_lower_bound hδ (fun s hs => lt_trans hδ (hδlt s hs))
          hδlt hclose (y i)).2
    exact hmin.trans hproduct
  · intro x hclose hxnn i
    have hmax := hMax i (Finset.mem_univ i)
    have hproduct : ∏ s ∈ Wᶜ, x s ^ (y i s) ≤ upper i := by
      simpa [upper] using prod_compl_upper_bound hxnn hclose (y i)
    have hmax' : upper i ≤ upper iMax := by simpa [upper] using hmax
    exact hproduct.trans hmax'

/-- A positive point on the relative interior of a coordinate face has a uniform positive margin
on the finitely many coordinates outside that face. -/
theorem exists_positive_complement_margin {W : Finset S} {z : Concentration S}
    (hz : ∀ s ∈ Wᶜ, 0 < z s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Wᶜ, δ < z s := by
  classical
  by_cases hne : (Wᶜ).Nonempty
  · rcases hne with ⟨s₀, hs₀⟩
    obtain ⟨smin, hsmin, hmin⟩ := Finset.exists_min_image Wᶜ z ⟨s₀, hs₀⟩
    refine ⟨z smin / 2, by linarith [hz smin hsmin], ?_⟩
    intro s hs
    have hzs : z smin ≤ z s := hmin s hs
    linarith [hz smin hsmin]
  · refine ⟨1, by norm_num, ?_⟩
    intro s hs
    exact (hne ⟨s, hs⟩).elim

/-- Choose the face-coordinate radius and the common reactionwise comparison factor together.
The explicit slack term `+ 1` makes the radius small enough that the comparison factor times the
number of reactions is at most one. -/
theorem exists_small_facet_parameters {δ₀ Dmin Dmax C : ℝ} (n : ℕ)
    (hδ₀ : 0 < δ₀) (hDmin : 0 < Dmin) (hDmax : 0 < Dmax) (hC : 0 ≤ C) :
    ∃ ε θ : ℝ, 0 < ε ∧ ε ≤ δ₀ ∧ ε ≤ 1 ∧ 0 ≤ θ ∧
      θ * Dmin = ε * Dmax * C ∧ θ * (n : ℝ) ≤ 1 := by
  let M : ℝ := Dmax * C * (n : ℝ) + 1
  let ε : ℝ := min δ₀ (min 1 (Dmin / M))
  let θ : ℝ := ε * Dmax * C / Dmin
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ₀ (lt_min zero_lt_one (div_pos hDmin hMpos))
  have hεδ₀ : ε ≤ δ₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hεinner : ε ≤ min 1 (Dmin / M) := by
    dsimp [ε]
    exact min_le_right _ _
  have hε1 : ε ≤ 1 := hεinner.trans (min_le_left _ _)
  have hεdiv : ε ≤ Dmin / M := hεinner.trans (min_le_right _ _)
  have hεM : ε * M ≤ Dmin := (le_div_iff₀ hMpos).mp hεdiv
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hεpos.le hDmax.le) hC) hDmin.le
  have hθscale : θ * Dmin = ε * Dmax * C := by
    dsimp [θ]
    field_simp [ne_of_gt hDmin]
  have hprod : ε * Dmax * C * (n : ℝ) ≤ Dmin := by
    calc
      ε * Dmax * C * (n : ℝ) = ε * (Dmax * C * (n : ℝ)) := by ring
      _ ≤ ε * M := by
        apply mul_le_mul_of_nonneg_left _ hεpos.le
        dsimp [M]
        exact le_add_of_nonneg_right (by norm_num)
      _ ≤ Dmin := hεM
  have hsmall : θ * (n : ℝ) ≤ 1 := by
    calc
      θ * (n : ℝ) = (ε * Dmax * C * (n : ℝ)) / Dmin := by
        dsimp [θ]
        ring
      _ ≤ 1 := (div_le_iff₀ hDmin).2 (by simpa using hprod)
  exact ⟨ε, θ, hεpos, hεδ₀, hε1, hθ, hθscale, hsmall⟩

/-! ### Stage 3, assembly: the dominating term controls the sign -/

/-- **The scalar reduction.**  On `W`, where every reaction vector is `γ r • v`, the mass-action
field is `v s` times a single scalar sum.  This is the paper's `f_i(x) = v_i ∑_k γ_k κ_k x^{y_k}`,
and it reduces facet repulsion to a sign question about one real number. -/
theorem massActionVectorField_eq_of_proj (N : Network S) (κ : N.RateConstants)
    {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ}
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    (x : Concentration S) {s : S} (hs : s ∈ W) :
    N.massActionVectorField κ x s = v s * ∑ r : N.R, γ r * N.massActionRate κ r x := by
  rw [Network.massActionVectorField_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [hγ r s hs]
  ring

/-- A finite sum is nonnegative once the total negative part is dominated by the total
nonnegative part. -/
theorem sum_nonneg_of_negSum_le_posSum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (h : ∑ i ∈ Finset.univ.filter (fun i => a i < 0), (-(a i))
          ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ (a i < 0)), a i) :
    0 ≤ ∑ i, a i := by
  classical
  have hsplit : ∑ i, a i
      = (∑ i ∈ Finset.univ.filter (fun i => a i < 0), a i)
        + ∑ i ∈ Finset.univ.filter (fun i => ¬ (a i < 0)), a i :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => a i < 0) a).symm
  have hneg : ∑ i ∈ Finset.univ.filter (fun i => a i < 0), a i
      = -(∑ i ∈ Finset.univ.filter (fun i => a i < 0), (-(a i))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hneg]
  linarith

/-- **The dominating term wins.**  If one index `ℓ` carries a nonnegative value and every negative
value is at most `θ · a ℓ` in magnitude, with `θ` small enough that `θ` times the number of indices
is at most one, then the whole sum is nonnegative.

Applied with `a r = γ r · κ r · x^{y_r}`, `ℓ` the reaction out of the minimal complex, and `θ` the
factor `ε · Dmax / Dmin` supplied by `massActionMonomial_domination`, this is exactly the final step
of Anderson–Shiu Theorem 3.2: for `ε` small enough, `f_i(x) ≥ 0` for every `i ∈ W`. -/
theorem sum_nonneg_of_dominating_negatives {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ℓ : ι) (hℓ : 0 ≤ a ℓ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hdom : ∀ i, a i < 0 → -(a i) ≤ θ * a ℓ)
    (hsmall : θ * (Fintype.card ι : ℝ) ≤ 1) :
    0 ≤ ∑ i, a i := by
  classical
  refine sum_nonneg_of_negSum_le_posSum a ?_
  set Neg := Finset.univ.filter (fun i => a i < 0) with hNeg
  set Pos := Finset.univ.filter (fun i => ¬ (a i < 0)) with hPos
  -- the negative part is at most `card · θ · a ℓ ≤ a ℓ`
  have hnegle : ∑ i ∈ Neg, (-(a i)) ≤ (Neg.card : ℝ) * (θ * a ℓ) := by
    have := Finset.sum_le_card_nsmul Neg (fun i => -(a i)) (θ * a ℓ) ?_
    · simpa [nsmul_eq_mul] using this
    · intro i hi
      exact hdom i (Finset.mem_filter.mp hi).2
  have hcardle : (Neg.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have := Finset.card_le_card (Finset.filter_subset (fun i => a i < 0) Finset.univ)
    simpa [hNeg, Finset.card_univ] using (Nat.cast_le (α := ℝ)).mpr this
  have hθaℓ : 0 ≤ θ * a ℓ := mul_nonneg hθ hℓ
  have hstep : (Neg.card : ℝ) * (θ * a ℓ) ≤ a ℓ := by
    have h1 : (Neg.card : ℝ) * (θ * a ℓ) ≤ (Fintype.card ι : ℝ) * (θ * a ℓ) :=
      mul_le_mul_of_nonneg_right hcardle hθaℓ
    have h2 : (Fintype.card ι : ℝ) * (θ * a ℓ) = (θ * (Fintype.card ι : ℝ)) * a ℓ := by ring
    have h3 : (θ * (Fintype.card ι : ℝ)) * a ℓ ≤ 1 * a ℓ :=
      mul_le_mul_of_nonneg_right hsmall hℓ
    calc (Neg.card : ℝ) * (θ * a ℓ) ≤ (Fintype.card ι : ℝ) * (θ * a ℓ) := h1
      _ = (θ * (Fintype.card ι : ℝ)) * a ℓ := h2
      _ ≤ 1 * a ℓ := h3
      _ = a ℓ := one_mul _
  -- and `a ℓ` is one of the nonnegative terms
  have hℓPos : ℓ ∈ Pos := by
    rw [hPos, Finset.mem_filter]
    exact ⟨Finset.mem_univ ℓ, not_lt.mpr hℓ⟩
  have hposge : a ℓ ≤ ∑ i ∈ Pos, a i := by
    refine Finset.single_le_sum (f := a) ?_ hℓPos
    intro i hi
    exact not_lt.mp (Finset.mem_filter.mp hi).2
  linarith [hnegle, hstep, hposge]

/-- A reaction-by-reaction variant of `sum_nonneg_of_dominating_negatives`: each negative term
may be controlled by the entire nonnegative part of the sum, with a common factor `θ`. The factor
`θ * card ι ≤ 1` then makes the total negative part no larger than that nonnegative part. -/
theorem sum_nonneg_of_dominating_negatives_by_posSum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hdom : ∀ i, a i < 0 →
      -(a i) ≤ θ * ∑ j ∈ Finset.univ.filter (fun j => ¬ (a j < 0)), a j)
    (hsmall : θ * (Fintype.card ι : ℝ) ≤ 1) : 0 ≤ ∑ i, a i := by
  classical
  let Neg := Finset.univ.filter (fun i => a i < 0)
  let Pos := Finset.univ.filter (fun i => ¬ (a i < 0))
  have hposNN : 0 ≤ ∑ i ∈ Pos, a i :=
    Finset.sum_nonneg fun i hi => not_lt.mp (Finset.mem_filter.mp hi).2
  have hnegle : ∑ i ∈ Neg, (-(a i)) ≤ (Neg.card : ℝ) *
      (θ * ∑ i ∈ Pos, a i) := by
    have hsum := Finset.sum_le_card_nsmul Neg (fun i => -(a i))
      (θ * ∑ i ∈ Pos, a i) ?_
    · simpa [nsmul_eq_mul] using hsum
    · intro i hi
      apply hdom i
      exact (Finset.mem_filter.mp hi).2
  have hcardle : (Neg.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have hcard := Finset.card_le_card (Finset.filter_subset (fun i => a i < 0) Finset.univ)
    simpa [Neg, Finset.card_univ] using (Nat.cast_le (α := ℝ)).mpr hcard
  have hstep : (Neg.card : ℝ) * (θ * ∑ i ∈ Pos, a i) ≤ ∑ i ∈ Pos, a i := by
    calc
      (Neg.card : ℝ) * (θ * ∑ i ∈ Pos, a i)
          ≤ (Fintype.card ι : ℝ) * (θ * ∑ i ∈ Pos, a i) :=
            mul_le_mul_of_nonneg_right hcardle (mul_nonneg hθ hposNN)
      _ = (θ * (Fintype.card ι : ℝ)) * ∑ i ∈ Pos, a i := by ring
      _ ≤ 1 * ∑ i ∈ Pos, a i := mul_le_mul_of_nonneg_right hsmall hposNN
      _ = ∑ i ∈ Pos, a i := by ring
  apply sum_nonneg_of_negSum_le_posSum a
  change ∑ i ∈ Neg, (-(a i)) ≤ ∑ i ∈ Pos, a i
  exact hnegle.trans hstep


/-- **Anderson–Shiu facet repulsion, assembled from the verified pieces.**  This is Definition 3.1's
repulsion inequality `∑_{i ∈ W} x_i f_i(x) ≥ 0`, derived from:

* `hv` — stage 1's conclusion that the facet direction is positive on `W`;
* `hγ` — the facet condition that every reaction vector is `γ r • v` on `W`;
* `hℓ` — one reaction `ℓ` with a nonnegative contribution (the reaction out of the minimal complex,
  supplied by stage 2 plus weak reversibility);
* `hdom` — every negative contribution is at most `θ` times `ℓ`'s (supplied by
  `massActionMonomial_domination`);
* `hsmall` — `θ` small enough, which is where the radius `δ` of the ball around the facet-interior
  point `z` gets chosen.

Everything downstream of Theorem 3.2 in the paper — Corollary 3.3's finite cover, Theorem 3.4,
Lemma 4.5, Theorem 4.6 and Corollary 4.7 (GAC for `dim P = 2`) — sits on top of this inequality.
What is *not* yet formalized is the production of `hv`, `hγ`, `hℓ` and `hsmall` from facet-ness,
weak reversibility and facet-interiority; see `docs/persistence-gac.md`. -/
theorem facet_repelling_of_data (N : Network S) (κ : N.RateConstants)
    {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ} {x : Concentration S} {ℓ : N.R} {θ : ℝ}
    (hv : ∀ s ∈ W, 0 < v s)
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    (hxpos : ∀ s, 0 < x s)
    (hℓ : 0 ≤ γ ℓ * N.massActionRate κ ℓ x)
    (hθ : 0 ≤ θ)
    (hdom : ∀ r : N.R, γ r * N.massActionRate κ r x < 0 →
      -(γ r * N.massActionRate κ r x) ≤ θ * (γ ℓ * N.massActionRate κ ℓ x))
    (hsmall : θ * (Fintype.card N.R : ℝ) ≤ 1) :
    0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s := by
  classical
  have hscalar : 0 ≤ ∑ r : N.R, γ r * N.massActionRate κ r x :=
    sum_nonneg_of_dominating_negatives
      (fun r => γ r * N.massActionRate κ r x) ℓ hℓ hθ hdom hsmall
  refine Finset.sum_nonneg ?_
  intro s hs
  rw [N.massActionVectorField_eq_of_proj κ hγ x hs]
  exact mul_nonneg (hxpos s).le (mul_nonneg (hv s hs).le hscalar)

/-- Facet repulsion with reaction-specific dominating contributions. This is the algebraic
interface for weakly reversible components where different negative reactions may use different
increasing reactions: each negative coefficient is bounded by `θ` times the full nonnegative
contribution, and `θ * |R| ≤ 1` controls their sum. -/
theorem facet_repelling_of_reactionwise_data (N : Network S) (κ : N.RateConstants)
    {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ} {x : Concentration S} {θ : ℝ}
    (hv : ∀ s ∈ W, 0 < v s)
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    (hxpos : ∀ s, 0 < x s) (hθ : 0 ≤ θ)
    (hdom : ∀ r : N.R, γ r * N.massActionRate κ r x < 0 →
      -(γ r * N.massActionRate κ r x) ≤
        θ * ∑ q ∈ Finset.univ.filter
          (fun q : N.R => ¬ (γ q * N.massActionRate κ q x < 0)),
          γ q * N.massActionRate κ q x)
    (hsmall : θ * (Fintype.card N.R : ℝ) ≤ 1) :
    0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s := by
  classical
  have hscalar : 0 ≤ ∑ r : N.R, γ r * N.massActionRate κ r x :=
    sum_nonneg_of_dominating_negatives_by_posSum
      (fun r => γ r * N.massActionRate κ r x) hθ hdom hsmall
  refine Finset.sum_nonneg ?_
  intro s hs
  rw [N.massActionVectorField_eq_of_proj κ hγ x hs]
  exact mul_nonneg (hxpos s).le (mul_nonneg (hv s hs).le hscalar)

/-- Derive the reactionwise repulsion bounds from weak reversibility and uniform monomial and
coefficient comparisons. `Dmin` and `Dmax` control the complementary monomial factors; `hcoeff`
controls the finite rate-coefficient ratios; and `hθscale` calibrates the common factor used by the
reactionwise sum estimate. The remaining geometric work is to produce these uniform constants on
a neighborhood of a facet-interior point. -/
theorem facet_repelling_of_local_monomial_bounds (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ}
    {x : Concentration S} {ε Dmin Dmax C θ : ℝ}
    (hW : W.Nonempty)
    (hv : ∀ s ∈ W, 0 < v s)
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    (hxpos : ∀ s, 0 < x s)
    (hxW : ∀ s ∈ W, x s ≤ ε) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hDmin : 0 < Dmin) (hDmax : 0 < Dmax)
    (hcomplLo : ∀ r : N.R, Dmin ≤
      ∏ s ∈ Wᶜ, x s ^ (N.reaction r).source s)
    (hcomplHi : ∀ r : N.R,
      ∏ s ∈ Wᶜ, x s ^ (N.reaction r).source s ≤ Dmax)
    (hcoeff : ∀ r ℓ : N.R, γ r < 0 → 0 < γ ℓ →
      (∀ s ∈ W, (N.reaction ℓ).source s < (N.reaction r).source s) →
      -γ r * κ.k r ≤ C * (γ ℓ * κ.k ℓ))
    (hθ : 0 ≤ θ) (hθscale : θ * Dmin = ε * Dmax * C)
    (hsmall : θ * (Fintype.card N.R : ℝ) ≤ 1) :
    0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s := by
  classical
  let a (r : N.R) := γ r * N.massActionRate κ r x
  rcases hW with ⟨s₀, hs₀⟩
  have hdom : ∀ r : N.R, a r < 0 →
      -(a r) ≤ θ * ∑ q ∈ Finset.univ.filter (fun q => ¬ (a q < 0)), a q := by
    intro r hra
    have hrateR : 0 < N.massActionRate κ r x := N.massActionRate_pos κ r hxpos
    have hγR : γ r < 0 := by
      by_contra hnot
      have hγRnn : 0 ≤ γ r := le_of_not_gt hnot
      have hprod : 0 ≤ γ r * N.massActionRate κ r x := mul_nonneg hγRnn hrateR.le
      exact (not_lt_of_ge hprod) (by simpa [a] using hra)
    obtain ⟨ℓ, hγℓ, hℓbelow⟩ :=
      N.exists_positiveReaction_below_of_negativeReaction hwr hv hγ r hγR hs₀
    have hmono : Dmin * Complex.massActionMonomial (N.reaction r).source x ≤
        ε * Dmax * Complex.massActionMonomial (N.reaction ℓ).source x :=
      massActionMonomial_domination hxpos hxW hε0 hε1
        (fun s hs => (hℓbelow s hs).le) hs₀ (hℓbelow s₀ hs₀) hDmin
        (hcomplLo ℓ) (hcomplHi r)
    have hmℓ : 0 < Complex.massActionMonomial (N.reaction ℓ).source x :=
      Complex.massActionMonomial_pos hxpos _
    have hcoeffR : 0 ≤ -γ r * κ.k r :=
      mul_nonneg (neg_nonneg.mpr hγR.le) (κ.positive r).le
    have hmult : 0 ≤ ε * Dmax * Complex.massActionMonomial (N.reaction ℓ).source x :=
      mul_nonneg (mul_nonneg hε0.le hDmax.le) hmℓ.le
    have hscaled : Dmin * ((-γ r * κ.k r) *
        Complex.massActionMonomial (N.reaction r).source x) ≤
        (ε * Dmax * C) * ((γ ℓ * κ.k ℓ) *
          Complex.massActionMonomial (N.reaction ℓ).source x) := by
      calc
        Dmin * ((-γ r * κ.k r) * Complex.massActionMonomial (N.reaction r).source x)
            = (-γ r * κ.k r) *
                (Dmin * Complex.massActionMonomial (N.reaction r).source x) := by ring
        _ ≤ (-γ r * κ.k r) *
              (ε * Dmax * Complex.massActionMonomial (N.reaction ℓ).source x) :=
                mul_le_mul_of_nonneg_left hmono hcoeffR
        _ ≤ (C * (γ ℓ * κ.k ℓ)) *
              (ε * Dmax * Complex.massActionMonomial (N.reaction ℓ).source x) :=
                mul_le_mul_of_nonneg_right (hcoeff r ℓ hγR hγℓ hℓbelow) hmult
        _ = (ε * Dmax * C) *
              ((γ ℓ * κ.k ℓ) * Complex.massActionMonomial (N.reaction ℓ).source x) := by ring
    have hnegRate : -(a r) = (-γ r * κ.k r) *
        Complex.massActionMonomial (N.reaction r).source x := by
      simp [a, Network.massActionRate]
      ring
    have hposRate : a ℓ = (γ ℓ * κ.k ℓ) *
        Complex.massActionMonomial (N.reaction ℓ).source x := by
      simp [a, Network.massActionRate]
      ring
    have hscaled' : Dmin * (-(a r)) ≤ Dmin * (θ * a ℓ) := by
      calc
        Dmin * (-(a r)) = Dmin * ((-γ r * κ.k r) *
            Complex.massActionMonomial (N.reaction r).source x) := by rw [hnegRate]
        _ ≤ (ε * Dmax * C) * ((γ ℓ * κ.k ℓ) *
            Complex.massActionMonomial (N.reaction ℓ).source x) := hscaled
        _ = Dmin * (θ * a ℓ) := by rw [← hθscale, hposRate]; ring
    have hanchor : -(a r) ≤ θ * a ℓ := le_of_mul_le_mul_left hscaled' hDmin
    have hℓpos : 0 < a ℓ := mul_pos hγℓ (N.massActionRate_pos κ ℓ hxpos)
    have hℓmem : ℓ ∈ Finset.univ.filter (fun q : N.R => ¬ (a q < 0)) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, ?_⟩
      exact not_lt.mpr hℓpos.le
    have hposge : a ℓ ≤ ∑ q ∈ Finset.univ.filter (fun q : N.R => ¬ (a q < 0)), a q := by
      refine Finset.single_le_sum ?_ hℓmem
      intro q hq
      exact not_lt.mp (Finset.mem_filter.mp hq).2
    calc
      -(a r) ≤ θ * a ℓ := hanchor
      _ ≤ θ * ∑ q ∈ Finset.univ.filter (fun q : N.R => ¬ (a q < 0)), a q :=
        mul_le_mul_of_nonneg_left hposge hθ
  have hdom' : ∀ r : N.R, γ r * N.massActionRate κ r x < 0 →
      -(γ r * N.massActionRate κ r x) ≤
        θ * ∑ q ∈ Finset.univ.filter
          (fun q : N.R => ¬ (γ q * N.massActionRate κ q x < 0)),
          γ q * N.massActionRate κ q x := by
    intro r hr
    simpa [a] using hdom r (by simpa [a] using hr)
  exact N.facet_repelling_of_reactionwise_data κ hv hγ hxpos hθ hdom' hsmall

/-- Finite rate constants provide one coefficient comparison factor for every eligible ordered
pair. Only pairs with a negative first coefficient, a positive second coefficient, and the
required source ordering enter the finite sum defining `C`. -/
theorem exists_uniform_reaction_coefficient_bound (N : Network S) (κ : N.RateConstants)
    {W : Finset S} (γ : N.R → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ℓ : N.R, γ r < 0 → 0 < γ ℓ →
        (∀ s ∈ W, (N.reaction ℓ).source s < (N.reaction r).source s) →
        -γ r * κ.k r ≤ C * (γ ℓ * κ.k ℓ) := by
  classical
  let eligible : Finset (N.R × N.R) := Finset.univ.filter fun p =>
    γ p.1 < 0 ∧ 0 < γ p.2 ∧
      ∀ s ∈ W, (N.reaction p.2).source s < (N.reaction p.1).source s
  let ratio (p : N.R × N.R) : ℝ :=
    (-γ p.1 * κ.k p.1) / (γ p.2 * κ.k p.2)
  let C : ℝ := ∑ p ∈ eligible, ratio p
  have hratioPos (p : N.R × N.R) (hp : p ∈ eligible) : 0 < ratio p := by
    rcases Finset.mem_filter.mp hp with ⟨_, ⟨hneg, hpos, _⟩⟩
    dsimp [ratio]
    exact div_pos (mul_pos (neg_pos.mpr hneg) (κ.positive p.1))
      (mul_pos hpos (κ.positive p.2))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact Finset.sum_nonneg fun p hp => (hratioPos p hp).le
  · intro r ℓ hneg hpos hbelow
    have hp : (r, ℓ) ∈ eligible := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hneg, hpos, hbelow⟩
    have hratioSum : ratio (r, ℓ) ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum (fun p hp => (hratioPos p hp).le) hp
    have hden : 0 < γ ℓ * κ.k ℓ := mul_pos hpos (κ.positive ℓ)
    have hratio : (-γ r * κ.k r) / (γ ℓ * κ.k ℓ) ≤ C := by
      simpa [ratio] using hratioSum
    exact (div_le_iff₀ hden).mp hratio

/-- Uniform near-facet repulsion with every quantitative constant chosen from finiteness.

Given a weakly reversible network, a facet direction `v` on `W`, and a point `z` that vanishes on
`W` and is positive off `W`, there is one radius `ε > 0` such that every strictly positive `x`
within `ε` of `z` satisfies the Anderson–Shiu facet repulsion inequality. The proof obtains a
positive complementary-coordinate margin, bounds all finitely many reaction monomials there,
chooses a finite coefficient bound, and then selects `ε` and `θ` together so that
`θ · card R ≤ 1`. The geometric hypotheses producing `v` and the subsequent global finite-cover
and trajectory argument remain separate obligations. -/
theorem facet_repelling_near_facet_point (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {W : Finset S} {v : S → ℝ} {γ : N.R → ℝ}
    {z : Concentration S} (hW : W.Nonempty)
    (hv : ∀ s ∈ W, 0 < v s)
    (hγ : ∀ r, ∀ s ∈ W, N.reactionVector r s = γ r * v s)
    (hzW : ∀ s ∈ W, z s = 0)
    (hzpos : ∀ s ∈ Wᶜ, 0 < z s) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x : Concentration S, x.Positive →
        (∀ s, |x s - z s| ≤ ε) →
        0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s := by
  classical
  obtain ⟨δ₀, hδ₀, hδ₀lt⟩ := exists_positive_complement_margin hzpos
  obtain ⟨Dmin, Dmax, hDmin, hDmax, hlo, hhi⟩ :=
    exists_uniform_complement_monomial_bounds hδ₀ hδ₀lt
      (fun q : Option N.R => match q with
        | none => 0
        | some r => (N.reaction r).source)
  obtain ⟨C, hC, hcoeff⟩ := N.exists_uniform_reaction_coefficient_bound κ γ
  obtain ⟨ε, θ, hεpos, hεδ₀, hε1, hθ, hθscale, hsmall⟩ :=
    exists_small_facet_parameters (Fintype.card N.R) hδ₀ hDmin hDmax hC
  refine ⟨ε, hεpos, ?_⟩
  intro x hxpos hclose
  have hclose₀ : ∀ s, |x s - z s| ≤ δ₀ := by
    intro s
    exact (hclose s).trans hεδ₀
  have hxnn : ∀ s, 0 ≤ x s := fun s => (hxpos s).le
  have hcomplLo : ∀ r : N.R,
      Dmin ≤ ∏ s ∈ Wᶜ, x s ^ (N.reaction r).source s := by
    intro r
    simpa using hlo x hclose₀ hxnn (some r)
  have hcomplHi : ∀ r : N.R,
      ∏ s ∈ Wᶜ, x s ^ (N.reaction r).source s ≤ Dmax := by
    intro r
    simpa using hhi x hclose₀ hxnn (some r)
  have hxW : ∀ s ∈ W, x s ≤ ε := by
    intro s hs
    have hupper := (abs_le.mp (hclose s)).2
    rw [hzW s hs] at hupper
    simpa using hupper
  exact N.facet_repelling_of_local_monomial_bounds κ hwr hW hv hγ hxpos hxW
    hεpos hε1 hDmin hDmax hcomplLo hcomplHi hcoeff hθ hθscale hsmall

/-- The facet-rank condition and a compatible positive point supply the facet direction needed by
`facet_repelling_near_facet_point`. The compatibility argument also shows that no facet-direction
coordinate can vanish on `W`: otherwise every stoichiometric displacement vanishes there, which
contradicts the positive reference point and `z s = 0`. -/
theorem facet_repelling_near_facet_point_of_facet (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {W : Finset S}
    (hW : W.Nonempty)
    (hfacet : Module.finrank ℝ
        (LinearMap.ker ((projOn W).domRestrict N.stoichSubspace)) + 1
          = Module.finrank ℝ N.stoichSubspace)
    {x₀ z : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ z) (hznn : z.Nonnegative)
    (hzW : ∀ s ∈ W, z s = 0)
    (hzpos : ∀ s ∈ Wᶜ, 0 < z s) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x : Concentration S, x.Positive →
        (∀ s, |x s - z s| ≤ ε) →
        0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s := by
  have hnonvanish : ∀ v : S → ℝ,
      (∀ p ∈ N.stoichSubspace, ∃ c : ℝ, ∀ s ∈ W, p s = c * v s) →
      ∀ s ∈ W, v s ≠ 0 := by
    intro v hspan s hs hvs
    obtain ⟨c, hc⟩ := hspan (z - x₀) hcompat
    have hcoord : z s - x₀ s = c * v s := by
      simpa using hc s hs
    rw [hzW s hs, hvs, mul_zero] at hcoord
    have hxzero : x₀ s = 0 := by linarith
    exact (ne_of_gt (hx₀ s)) hxzero
  obtain ⟨v, γ, hv, hγ⟩ :=
    N.exists_facetDirection_pos_of_facet hfacet hx₀ hcompat hznn hzW hnonvanish
  exact N.facet_repelling_near_facet_point κ hwr hW hv hγ hzW hzpos

/-- A positive orbit cannot converge to a face point when the facet estimate makes the squared
mass of the vanishing coordinates nondecreasing nearby. The squared mass stays positive at every
finite time, while convergence to the face would force it to zero. -/
theorem no_convergent_positive_orbit_to_repelling_face (N : Network S) (κ : N.RateConstants)
    {W : Finset S} {z : Concentration S} {γ : ℝ → Concentration S}
    (hW : W.Nonempty) (hzW : ∀ s ∈ W, z s = 0)
    (hpos : ∀ t, 0 ≤ t → (γ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {ε : ℝ} (hε : 0 < ε)
    (hrepel : ∀ x : Concentration S, x.Positive →
      (∀ s, |x s - z s| ≤ ε) →
        0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s)
    (hlim : Tendsto γ atTop (𝓝 z)) :
    False := by
  let q : ℝ → ℝ := fun t => ∑ s ∈ W, (γ t s) ^ 2
  have hclose : ∀ᶠ t in atTop, ∀ s, |γ t s - z s| ≤ ε := by
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds z hε)] with t ht s
    have hnorm : dist (γ t) z < ε := Metric.mem_ball.mp ht
    exact le_of_lt (calc
      |γ t s - z s| = ‖(γ t - z) s‖ := by rw [Real.norm_eq_abs]; rfl
      _ ≤ ‖γ t - z‖ := norm_le_pi_norm _ _
      _ = dist (γ t) z := by rw [dist_eq_norm]
      _ < ε := hnorm)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hclose
  let T : ℝ := max T₀ 0
  have hTnonneg : 0 ≤ T := le_max_right _ _
  have hTclose : ∀ t, T ≤ t → ∀ s, |γ t s - z s| ≤ ε := by
    intro t ht s
    exact hT₀ t (le_trans (le_max_left _ _) ht) s
  have hqderiv : ∀ t, T ≤ t → HasDerivAt q
      (∑ s ∈ W, (2 * γ t s) * N.massActionVectorField κ (γ t) s) t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hTnonneg ht
    have hcoord : ∀ s, HasDerivAt (fun u => γ u s)
        (N.massActionVectorField κ (γ t) s) t := by
      intro s
      exact (hasDerivAt_pi.mp (hsol t ht0)) s
    have hterm : ∀ s, HasDerivAt (fun u => (γ u s) ^ 2)
        ((2 * γ t s) * N.massActionVectorField κ (γ t) s) t := by
      intro s
      convert (hcoord s).pow 2 using 1
      ring
    have hsum : HasDerivAt (fun u => ∑ s ∈ W, (γ u s) ^ 2)
        (∑ s ∈ W, (2 * γ t s) * N.massActionVectorField κ (γ t) s) t :=
      HasDerivAt.fun_sum (fun s _ => hterm s)
    simpa [q] using hsum
  have hqcont : ContinuousOn q (Set.Ici T) := by
    intro t ht
    exact (hqderiv t (by simpa using ht)).continuousAt.continuousWithinAt
  have hqdiff : DifferentiableOn ℝ q (interior (Set.Ici T)) := by
    intro t ht
    exact (hqderiv t (le_of_lt (by simpa using ht))).differentiableAt.differentiableWithinAt
  have hqmono : MonotoneOn q (Set.Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T) hqcont hqdiff
    intro t ht
    have htT : T < t := by simpa using ht
    have hderiv := (hqderiv t htT.le).deriv
    rw [hderiv]
    have hnonneg := hrepel (γ t) (hpos t (le_trans hTnonneg htT.le))
      (hTclose t htT.le)
    have hfactor :
        (∑ s ∈ W, (2 * γ t s) * N.massActionVectorField κ (γ t) s) =
          2 * ∑ s ∈ W, γ t s * N.massActionVectorField κ (γ t) s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    rw [hfactor]
    exact mul_nonneg (by norm_num) hnonneg
  have hqpos : 0 < q T := by
    dsimp [q]
    obtain ⟨s, hs⟩ := hW
    exact Finset.sum_pos' (fun u hu => sq_nonneg (γ T u))
      ⟨s, hs, sq_pos_of_pos (hpos T hTnonneg s)⟩
  have hqzero : Tendsto q atTop (𝓝 0) := by
    have hterm : ∀ s ∈ W, Tendsto (fun t => (γ t s) ^ 2) atTop (𝓝 0) := by
      intro s hs
      have hscoord := (tendsto_pi_nhds.mp hlim) s
      rw [hzW s hs] at hscoord
      simpa using hscoord.pow 2
    simpa [q] using tendsto_finsetSum W hterm
  have hsmall : ∀ᶠ t in atTop, q t < q T :=
    hqzero.eventually (Iio_mem_nhds hqpos)
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.mp hsmall
  let u := max T t
  have hTu : T ≤ u := le_max_left _ _
  have htu : t ≤ u := le_max_right _ _
  have hqu : q u < q T := ht u htu
  have hmon : q T ≤ q u := hqmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hTu) hTu
  exact (not_lt_of_ge hmon) hqu

/-- **Local facet repulsion excludes a recurrent omega-limit face.** Let `W` be a fixed nonempty
coordinate set, and suppose every omega-limit point lies on its zero face. If each omega-limit
point has some neighborhood on which the squared `W`-mass has nonnegative derivative, then the
positive orbit cannot accumulate on that face. Compactness is the recurrence bridge: the union of
the local neighborhoods covers the omega-limit set, so the orbit eventually stays in that union;
the squared `W`-mass is then nondecreasing, while omega accumulation on the zero face forces it
arbitrarily close to zero.

This handles repeated returns when one common face contains the full omega-limit set. It does not
assume that a single local estimate at one point covers the whole omega-limit set. -/
theorem no_omegaLimit_on_face_of_locally_repelling (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {W : Finset S} (hW : W.Nonempty)
    (hface : ∀ z ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ W, z s = 0)
    (hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hlocal : ∀ z ∈ omegaLimit atTop ϕ {x₀}, ∃ ε : ℝ, 0 < ε ∧
      ∀ x : Concentration S, x.Positive → (∀ s, |x s - z s| ≤ ε) →
        0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s) :
    False := by
  classical
  let Ω : Set (Concentration S) := omegaLimit atTop ϕ {x₀}
  let U : Set (Concentration S) :=
    ⋃ z : {z : Concentration S // z ∈ Ω},
      Metric.ball z.1 (Classical.choose (hlocal z.1 z.2) / 2)
  have hUopen : IsOpen U := isOpen_iUnion fun z => Metric.isOpen_ball
  have hΩU : Ω ⊆ U := by
    intro z hz
    apply Set.mem_iUnion.2
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    have hε := (Classical.choose_spec (hlocal z hz)).1
    linarith
  let ψ : ℝ≥0 → Concentration S := fun t => ϕ t x₀
  have hUevent : ∀ᶠ t : ℝ≥0 in atTop, ψ t ∈ U := by
    by_contra hnot
    have hfrequent : ∃ᶠ t : ℝ≥0 in atTop, ψ t ∉ U := by
      rw [Filter.not_eventually] at hnot
      exact hnot
    let Kbad : Set (Concentration S) := K ∩ Uᶜ
    have hKbad : IsCompact Kbad := hK.inter_right (isClosed_compl_iff.mpr hUopen)
    have hfrequentBad : ∃ᶠ t : ℝ≥0 in atTop, ψ t ∈ Kbad := by
      have hboth := hfrequent.and_eventually (Filter.Eventually.of_forall hmaps)
      exact hboth.mono fun t ht => ⟨ht.2, ht.1⟩
    obtain ⟨y, hyKbad, hycluster⟩ := hKbad.exists_mapClusterPt_of_frequently hfrequentBad
    have hyΩ : y ∈ Ω := by
      apply (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ x₀ y).2
      exact hycluster
    exact hyKbad.2 (hΩU hyΩ)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hUevent
  let T : ℝ := max (T₀ : ℝ) 0
  have hTnonneg : 0 ≤ T := le_max_right _ _
  have hT₀le : (T₀ : ℝ) ≤ T := le_max_left _ _
  have hUtail : ∀ t : ℝ, T ≤ t → γ x₀ t ∈ U := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hTnonneg ht
    let tNN : ℝ≥0 := ⟨t, ht0⟩
    have hge : T₀ ≤ tNN := by
      exact_mod_cast le_trans hT₀le ht
    have hmem := hT₀ tNN hge
    simpa [ψ] using (hϕγ x₀ tNN).symm ▸ hmem
  let q : ℝ → ℝ := fun t => ∑ s ∈ W, (γ x₀ t s) ^ 2
  have hqderiv : ∀ t, T ≤ t → HasDerivAt q
      (∑ s ∈ W, (2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hTnonneg ht
    have hcoord : ∀ s, HasDerivAt (fun u => γ x₀ u s)
        (N.massActionVectorField κ (γ x₀ t) s) t := by
      intro s
      exact (hasDerivAt_pi.mp (hsol t ht0)) s
    have hterm : ∀ s, HasDerivAt (fun u => (γ x₀ u s) ^ 2)
        ((2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) t := by
      intro s
      convert (hcoord s).pow 2 using 1
      ring
    have hsum : HasDerivAt (fun u => ∑ s ∈ W, (γ x₀ u s) ^ 2)
        (∑ s ∈ W, (2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) t :=
      HasDerivAt.fun_sum (fun s hs => hterm s)
    simpa [q] using hsum
  have hqcont : ContinuousOn q (Set.Ici T) := by
    intro t ht
    exact (hqderiv t (by simpa using ht)).continuousAt.continuousWithinAt
  have hqdiff : DifferentiableOn ℝ q (interior (Set.Ici T)) := by
    intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact (hqderiv t ht.le).differentiableAt.differentiableWithinAt
  have hqmono : MonotoneOn q (Set.Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T) hqcont hqdiff
    intro t ht
    have htT : T < t := by simpa using ht
    have ht0 : 0 ≤ t := le_trans hTnonneg htT.le
    rw [(hqderiv t htT.le).deriv]
    obtain ⟨z, hzball⟩ := Set.mem_iUnion.mp (hUtail t htT.le)
    obtain ⟨hε, hrepel⟩ := Classical.choose_spec (hlocal z.1 z.2)
    have hdist : dist (γ x₀ t) z.1 < Classical.choose (hlocal z.1 z.2) / 2 :=
      Metric.mem_ball.mp hzball
    have hclose : ∀ s, |γ x₀ t s - z.1 s| ≤ Classical.choose (hlocal z.1 z.2) := by
      intro s
      have hcoord : |γ x₀ t s - z.1 s| ≤ dist (γ x₀ t) z.1 := by
        calc
          |γ x₀ t s - z.1 s| = ‖(γ x₀ t - z.1) s‖ := by rw [Real.norm_eq_abs]; rfl
          _ ≤ ‖γ x₀ t - z.1‖ := norm_le_pi_norm _ _
          _ = dist (γ x₀ t) z.1 := by rw [dist_eq_norm]
      have hhalf : Classical.choose (hlocal z.1 z.2) / 2 ≤
          Classical.choose (hlocal z.1 z.2) := by linarith [hε]
      exact le_trans hcoord (le_trans hdist.le hhalf)
    have hnonneg := hrepel (γ x₀ t) (hpos t ht0) hclose
    have hfactor :
        (∑ s ∈ W, (2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) =
          2 * ∑ s ∈ W, γ x₀ t s * N.massActionVectorField κ (γ x₀ t) s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    rw [hfactor]
    exact mul_nonneg (by norm_num) hnonneg
  have hqpos : 0 < q T := by
    dsimp [q]
    obtain ⟨s, hs⟩ := hW
    exact Finset.sum_pos' (fun u hu => sq_nonneg (γ x₀ T u))
      ⟨s, hs, sq_pos_of_pos (hpos T hTnonneg s)⟩
  let qState : Concentration S → ℝ := fun x => ∑ s ∈ W, (x s) ^ 2
  have hqStateCont : Continuous qState :=
    continuous_finsetSum _ fun s _ => (continuous_apply s).pow 2
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro y ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, Filter.univ_mem,
      (IsClosed.closure_subset_iff hK.isClosed).mpr hsubK⟩
  obtain ⟨w, hw⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs
      (Set.singleton_nonempty x₀)
  have hqw : qState w = 0 := by
    dsimp [qState]
    apply Finset.sum_eq_zero
    intro s hs
    rw [hface w hw s hs]
    norm_num
  have hcluster : ClusterPt (qState w)
      (Filter.map (fun t : ℝ≥0 => qState (ϕ t x₀)) atTop) := by
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hw
    exact hw.continuousAt_comp hqStateCont.continuousAt
  have hopen : Set.Iio (q T) ∈ 𝓝 (qState w) := by
    rw [hqw]
    exact Iio_mem_nhds hqpos
  have hev : Set.Ici (q T) ∈
      Filter.map (fun t : ℝ≥0 => qState (ϕ t x₀)) atTop := by
    rw [Filter.mem_map]
    refine Filter.eventually_atTop.mpr ⟨⟨T, hTnonneg⟩, ?_⟩
    intro t ht
    have htT : T ≤ (t : ℝ) := by exact_mod_cast ht
    have hmono := hqmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr htT) htT
    change qState (ϕ t x₀) ∈ Set.Ici (q T)
    rw [hϕγ x₀ t]
    simpa [q, qState] using hmono
  haveI hne : (𝓝 (qState w) ⊓
      Filter.map (fun t : ℝ≥0 => qState (ϕ t x₀)) atTop).NeBot := hcluster
  have hmem := Filter.inter_mem (Filter.mem_inf_of_left hopen) (Filter.mem_inf_of_right hev)
  have hdisj : Set.Iio (q T) ∩ Set.Ici (q T) = (∅ : Set ℝ) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hy
    exact not_le.mpr hy
  rw [hdisj] at hmem
  exact Filter.empty_notMem _ hmem

/-- **A locally repelling face cannot meet the omega-limit set.** Unlike
`no_omegaLimit_on_face_of_locally_repelling`, the omega-limit set need not be contained in the
face. It is enough that the face meets the omega-limit set and that every omega-limit point on the
face has a local repulsion neighborhood for the same coordinate set. Compactness gives a positive
lower bound for the squared face mass away from those neighborhoods. The orbit is eventually in
the neighborhoods or above that lower bound, so it cannot make recurrent returns to the face. -/
theorem no_omegaLimit_meets_locally_repelling_face (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {W : Finset S} (hW : W.Nonempty)
    (hboundary : ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ W, z s = 0)
    (hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hlocal : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ W, z s = 0) →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ x : Concentration S, x.Positive → (∀ s, |x s - z s| ≤ ε) →
          0 ≤ ∑ s ∈ W, x s * N.massActionVectorField κ x s) :
    False := by
  classical
  let Ω : Set (Concentration S) := omegaLimit atTop ϕ {x₀}
  let qState : Concentration S → ℝ := fun x => ∑ s ∈ W, (x s) ^ 2
  have hqStateCont : Continuous qState :=
    continuous_finsetSum _ fun s _ => (continuous_apply s).pow 2
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro y ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have hclosureK : closure (Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀}) ⊆ K :=
    (IsClosed.closure_subset_iff hK.isClosed).mpr hsubK
  have hΩsubK : Ω ⊆ K := by
    exact (omegaLimit_subset_closure_image2 atTop ϕ {x₀} Filter.univ_mem).trans hclosureK
  have hΩcompact : IsCompact Ω :=
    hK.of_isClosed_subset (isClosed_omegaLimit atTop ϕ {x₀}) hΩsubK
  let U : Set (Concentration S) :=
    ⋃ z : {z : Concentration S // z ∈ Ω ∧ ∀ s ∈ W, z s = 0},
      Metric.ball z.1 (Classical.choose (hlocal z.1 z.2.1 z.2.2) / 2)
  have hUopen : IsOpen U := isOpen_iUnion fun z => Metric.isOpen_ball
  have hfaceU : ∀ z ∈ Ω, (∀ s ∈ W, z s = 0) → z ∈ U := by
    intro z hz hzero
    apply Set.mem_iUnion.2
    refine ⟨⟨z, hz, hzero⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    have hε := (Classical.choose_spec (hlocal z hz hzero)).1
    linarith
  let C : Set (Concentration S) := Ω ∩ Uᶜ
  have hCcompact : IsCompact C :=
    hΩcompact.inter_right (isClosed_compl_iff.mpr hUopen)
  have hqCpos : ∀ z ∈ C, 0 < qState z := by
    intro z hz
    have hqnn : 0 ≤ qState z := by
      dsimp [qState]
      exact Finset.sum_nonneg fun s hs => sq_nonneg (z s)
    by_contra hnot
    have hqzero : qState z = 0 := le_antisymm (not_lt.mp hnot) hqnn
    have hzero : ∀ s ∈ W, z s = 0 := by
      intro s hs
      have hterm : (z s) ^ 2 ≤ qState z := by
        dsimp [qState]
        exact Finset.single_le_sum (fun u hu => sq_nonneg (z u)) hs
      rw [hqzero] at hterm
      nlinarith [sq_nonneg (z s)]
    exact hz.2 (hfaceU z hz.1 hzero)
  obtain ⟨δ, hδpos, hδlower⟩ :=
    hCcompact.exists_forall_le' (a := 0) hqStateCont.continuousOn hqCpos
  let a : ℝ := δ / 2
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have ha_lt_δ : a < δ := by dsimp [a]; linarith
  have hΩlower : ∀ z ∈ Ω, z ∉ U → δ ≤ qState z := by
    intro z hz hnot
    exact hδlower z ⟨hz, hnot⟩
  let V : Set (Concentration S) := U ∪ qState ⁻¹' Set.Ici a
  let ψ : ℝ≥0 → Concentration S := fun t => ϕ t x₀
  have hVevent : ∀ᶠ t : ℝ≥0 in atTop, ψ t ∈ V := by
    by_contra hnot
    have hfrequent : ∃ᶠ t : ℝ≥0 in atTop, ψ t ∉ V := by
      rw [Filter.not_eventually] at hnot
      exact hnot
    let Kbad : Set (Concentration S) := K ∩ (Uᶜ ∩ qState ⁻¹' Set.Iic a)
    have hbadclosed : IsClosed (Uᶜ ∩ qState ⁻¹' Set.Iic a) :=
      (isClosed_compl_iff.mpr hUopen).inter (isClosed_Iic.preimage hqStateCont)
    have hKbad : IsCompact Kbad := hK.inter_right hbadclosed
    have hfrequentBad : ∃ᶠ t : ℝ≥0 in atTop, ψ t ∈ Kbad := by
      have hboth := hfrequent.and_eventually (Filter.Eventually.of_forall hmaps)
      exact hboth.mono fun t ht => by
        have hnotV : ψ t ∉ U ∪ qState ⁻¹' Set.Ici a := by simpa [V] using ht.1
        simp only [Set.mem_union, Set.mem_preimage, Set.mem_Ici, not_or] at hnotV
        have hqle : qState (ψ t) ≤ a := (lt_of_not_ge hnotV.2).le
        exact ⟨ht.2, hnotV.1, hqle⟩
    obtain ⟨y, hyKbad, hycluster⟩ := hKbad.exists_mapClusterPt_of_frequently hfrequentBad
    have hyΩ : y ∈ Ω := by
      apply (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ x₀ y).2
      exact hycluster
    have hδy := hΩlower y hyΩ hyKbad.2.1
    have hqy : qState y ≤ a := hyKbad.2.2
    have : δ ≤ a := le_trans hδy hqy
    linarith
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hVevent
  let T : ℝ := max (T₀ : ℝ) 0
  have hTnonneg : 0 ≤ T := le_max_right _ _
  have hT₀le : (T₀ : ℝ) ≤ T := le_max_left _ _
  have hVtail : ∀ t : ℝ, T ≤ t → γ x₀ t ∈ V := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hTnonneg ht
    let tNN : ℝ≥0 := ⟨t, ht0⟩
    have hge : T₀ ≤ tNN := by
      exact_mod_cast le_trans hT₀le ht
    have hmem := hT₀ tNN hge
    simpa [ψ] using (hϕγ x₀ tNN).symm ▸ hmem
  let q : ℝ → ℝ := fun t => qState (γ x₀ t)
  have hqderiv : ∀ t, T ≤ t → HasDerivAt q
      (∑ s ∈ W, (2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hTnonneg ht
    have hcoord : ∀ s, HasDerivAt (fun u => γ x₀ u s)
        (N.massActionVectorField κ (γ x₀ t) s) t := by
      intro s
      exact (hasDerivAt_pi.mp (hsol t ht0)) s
    have hterm : ∀ s, HasDerivAt (fun u => (γ x₀ u s) ^ 2)
        ((2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) t := by
      intro s
      convert (hcoord s).pow 2 using 1
      ring
    have hsum : HasDerivAt (fun u => ∑ s ∈ W, (γ x₀ u s) ^ 2)
        (∑ s ∈ W, (2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) t :=
      HasDerivAt.fun_sum (fun s hs => hterm s)
    simpa [q, qState] using hsum
  have hqcont : ContinuousOn q (Set.Ici T) := by
    intro t ht
    exact (hqderiv t (by simpa using ht)).continuousAt.continuousWithinAt
  have hqdiff : DifferentiableOn ℝ q (interior (Set.Ici T)) := by
    intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact (hqderiv t ht.le).differentiableAt.differentiableWithinAt
  have hqderiv_nonneg : ∀ t, T ≤ t → q t < a → 0 ≤ deriv q t := by
    intro t ht hqt
    rw [(hqderiv t ht).deriv]
    have hstate : γ x₀ t ∈ U := by
      have hV := hVtail t ht
      change γ x₀ t ∈ U ∪ qState ⁻¹' Set.Ici a at hV
      rcases hV with hU | hhigh
      · exact hU
      · change a ≤ qState (γ x₀ t) at hhigh
        change qState (γ x₀ t) < a at hqt
        exact (not_lt_of_ge hhigh hqt).elim
    obtain ⟨z, hzball⟩ := Set.mem_iUnion.mp hstate
    obtain ⟨hε, hrepel⟩ := Classical.choose_spec (hlocal z.1 z.2.1 z.2.2)
    have hdist : dist (γ x₀ t) z.1 <
        Classical.choose (hlocal z.1 z.2.1 z.2.2) / 2 := Metric.mem_ball.mp hzball
    have hclose : ∀ s, |γ x₀ t s - z.1 s| ≤ Classical.choose (hlocal z.1 z.2.1 z.2.2) := by
      intro s
      have hcoord : |γ x₀ t s - z.1 s| ≤ dist (γ x₀ t) z.1 := by
        calc
          |γ x₀ t s - z.1 s| = ‖(γ x₀ t - z.1) s‖ := by rw [Real.norm_eq_abs]; rfl
          _ ≤ ‖γ x₀ t - z.1‖ := norm_le_pi_norm _ _
          _ = dist (γ x₀ t) z.1 := by rw [dist_eq_norm]
      have hhalf : Classical.choose (hlocal z.1 z.2.1 z.2.2) / 2 ≤
          Classical.choose (hlocal z.1 z.2.1 z.2.2) := by linarith [hε]
      exact le_trans hcoord (le_trans hdist.le hhalf)
    have ht0 : 0 ≤ t := le_trans hTnonneg ht
    have hnonneg := hrepel (γ x₀ t) (hpos t ht0) hclose
    have hfactor :
        (∑ s ∈ W, (2 * γ x₀ t s) * N.massActionVectorField κ (γ x₀ t) s) =
          2 * ∑ s ∈ W, γ x₀ t s * N.massActionVectorField κ (γ x₀ t) s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    rw [hfactor]
    exact mul_nonneg (by norm_num) hnonneg
  have hqpos : 0 < q T := by
    dsimp [q, qState]
    obtain ⟨s, hs⟩ := hW
    exact Finset.sum_pos' (fun u hu => sq_nonneg (γ x₀ T u))
      ⟨s, hs, sq_pos_of_pos (hpos T hTnonneg s)⟩
  let b : ℝ := min (q T) a / 2
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hbqT : b < q T := by
    dsimp [b]
    have hmin : min (q T) a ≤ q T := min_le_left _ _
    linarith
  have hba : b < a := by
    dsimp [b]
    have hmin : min (q T) a ≤ a := min_le_right _ _
    linarith
  have hbarrier : ∀ t, T ≤ t → b ≤ q t := by
    intro t ht
    by_contra hnot
    have hqtb : q t < b := lt_of_not_ge hnot
    have hTlt : T < t := by
      by_contra h
      have hle : t ≤ T := le_of_not_gt h
      have heq : t = T := le_antisymm hle ht
      subst t
      exact (not_lt_of_ge hbqT.le) hqtb
    have hqcontTt : ContinuousOn q (Set.Icc T t) :=
      hqcont.mono (by intro u hu; exact hu.1)
    have hbIcc : b ∈ Set.Icc (q t) (q T) := ⟨hqtb.le, hbqT.le⟩
    obtain ⟨s, hsIcc, hqs⟩ :=
      (intermediate_value_Icc' hTlt.le hqcontTt) hbIcc
    let E : Set ℝ := Set.Icc T t ∩ q ⁻¹' {b}
    have hEclosed : IsClosed E := by
      dsimp [E]
      exact hqcontTt.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hEcompact : IsCompact E :=
      isCompact_Icc.of_isClosed_subset hEclosed (by intro u hu; exact hu.1)
    have hEne : E.Nonempty := by
      refine ⟨s, ?_⟩
      dsimp [E]
      exact ⟨hsIcc, by simpa using hqs⟩
    obtain ⟨s₀, hs₀E, hs₀max⟩ :=
      hEcompact.exists_isMaxOn hEne continuous_id.continuousOn
    have hs₀ : s₀ ∈ Set.Icc T t ∧ q s₀ = b := by
      simpa [E, Set.mem_preimage] using hs₀E
    have hqbelow : ∀ u ∈ Set.Icc s₀ t, q u ≤ b := by
      intro u hu
      by_contra hnotu
      have hbu : b < q u := lt_of_not_ge hnotu
      have hs₀u : s₀ < u := by
        by_contra h
        have hus₀ : u ≤ s₀ := le_of_not_gt h
        have heq : u = s₀ := le_antisymm hus₀ hu.1
        subst u
        rw [hs₀.2] at hbu
        exact (lt_irrefl _ hbu)
      have hqcontut : ContinuousOn q (Set.Icc u t) := hqcont.mono (by
        intro v hv
        exact le_trans (le_trans hs₀.1.1 hu.1) hv.1)
      have hbIccut : b ∈ Set.Icc (q t) (q u) := ⟨hqtb.le, hbu.le⟩
      obtain ⟨v, hvIcc, hqv⟩ :=
        (intermediate_value_Icc' hu.2 hqcontut) hbIccut
      have hvE : v ∈ E := by
        dsimp [E]
        refine ⟨⟨le_trans (le_trans hs₀.1.1 hu.1) hvIcc.1,
          hvIcc.2⟩, ?_⟩
        simpa using hqv
      have hvle : v ≤ s₀ := by simpa using hs₀max hvE
      exact (not_le_of_gt (lt_of_lt_of_le hs₀u hvIcc.1)) hvle
    have hqcontSt : ContinuousOn q (Set.Icc s₀ t) := hqcont.mono (by
      intro u hu
      exact le_trans hs₀.1.1 hu.1)
    have hqdiffSt : DifferentiableOn ℝ q (interior (Set.Icc s₀ t)) := by
      intro u hu
      have hucc : u ∈ Set.Icc s₀ t := interior_subset hu
      exact (hqderiv u (le_trans hs₀.1.1 hucc.1)).differentiableAt.differentiableWithinAt
    have hmonoSt : MonotoneOn q (Set.Icc s₀ t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s₀ t) hqcontSt hqdiffSt
      intro u hu
      have hucc : u ∈ Set.Icc s₀ t := interior_subset hu
      have hqu : q u < a := lt_of_le_of_lt (hqbelow u hucc) hba
      exact hqderiv_nonneg u (le_trans hs₀.1.1 hucc.1) hqu
    have hmono := hmonoSt ⟨le_rfl, hs₀.1.2⟩ ⟨hs₀.1.2, le_rfl⟩ hs₀.1.2
    rw [hs₀.2] at hmono
    exact (not_lt_of_ge hmono) hqtb
  obtain ⟨w, hw, hzero⟩ := hboundary
  have hqw : qState w = 0 := by
    dsimp [qState]
    apply Finset.sum_eq_zero
    intro s hs
    rw [hzero s hs]
    norm_num
  have hcluster : ClusterPt (qState w)
      (Filter.map (fun t : ℝ≥0 => qState (ϕ t x₀)) atTop) := by
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hw
    exact hw.continuousAt_comp hqStateCont.continuousAt
  have hopen : Set.Iio b ∈ 𝓝 (qState w) := by
    rw [hqw]
    exact Iio_mem_nhds hbpos
  have hev : Set.Ici b ∈
      Filter.map (fun t : ℝ≥0 => qState (ϕ t x₀)) atTop := by
    rw [Filter.mem_map]
    refine Filter.eventually_atTop.mpr ⟨⟨T, hTnonneg⟩, ?_⟩
    intro t ht
    have htT : T ≤ (t : ℝ) := by exact_mod_cast ht
    have hbar := hbarrier t htT
    change qState (ϕ t x₀) ∈ Set.Ici b
    rw [hϕγ x₀ t]
    simpa [q, qState] using hbar
  haveI hne : (𝓝 (qState w) ⊓
      Filter.map (fun t : ℝ≥0 => qState (ϕ t x₀)) atTop).NeBot := hcluster
  have hmem := Filter.inter_mem (Filter.mem_inf_of_left hopen) (Filter.mem_inf_of_right hev)
  have hdisj : Set.Iio b ∩ Set.Ici b = (∅ : Set ℝ) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hy
    exact not_le.mpr hy
  rw [hdisj] at hmem
  exact Filter.empty_notMem _ hmem

/-- A convergent positive mass-action orbit cannot approach a codimension-one compatibility
face when the Anderson--Shiu facet hypotheses hold. This gives convergence exclusion at a
relative-interior facet point; excluding a point from a general omega-limit set also requires
controlling repeated returns to its neighborhood. -/
theorem no_convergent_positive_orbit_to_facet (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {W : Finset S} (hW : W.Nonempty)
    (hfacet : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict N.stoichSubspace)) + 1
        = Module.finrank ℝ N.stoichSubspace)
    {x₀ z : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ z) (hznn : z.Nonnegative)
    (hzW : ∀ s ∈ W, z s = 0) (hzpos : ∀ s ∈ Wᶜ, 0 < z s)
    {γ : ℝ → Concentration S} (hpos : ∀ t, 0 ≤ t → (γ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hlim : Tendsto γ atTop (𝓝 z)) :
    False := by
  obtain ⟨ε, hε, hrepel⟩ := N.facet_repelling_near_facet_point_of_facet κ hwr hW hfacet
    hx₀ hcompat hznn hzW hzpos
  exact N.no_convergent_positive_orbit_to_repelling_face κ hW hzW hpos hsol hε hrepel hlim

end Network
end CRNT
