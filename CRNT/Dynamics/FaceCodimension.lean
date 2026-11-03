import CRNT.Dynamics.FacetRepulsionAndersonShiu

/-!
# Codimension of a coordinate face inside the stoichiometric subspace

`CRNT.Dynamics.FacetRepulsionAndersonShiu` proves the Anderson--Shiu near-facet repulsion
estimate under the *facet* hypothesis

```
finrank (ker ((projOn W).domRestrict N.stoichSubspace)) + 1 = finrank N.stoichSubspace,
```

equivalently `finrank (N.stoichSubspace.map (projOn W)) = 1`.  The Global Attractor Theorem
splits on that hypothesis, and the branch where it fails is the remaining hole.  This module
analyses that branch: it shows the failure is *never* a codimension-zero failure, so the only
surviving case is codimension `≥ 2`, and it records the two consequences the residual argument
gets for free.

## Contents

* `map_projOn_eq_bot_of_ker_finrank_eq`, `eq_zero_of_mem_of_ker_finrank_eq`:
  rank--nullity in the degenerate direction.  A full-dimensional kernel means the `W`-projection
  of the subspace is trivial, i.e. *every* stoichiometric displacement vanishes on `W`.
* `one_le_finrank_map_projOn`: a single nonvanishing coordinate witness forces the projection
  to be at least a line.  Together with the previous item this rules out codimension zero.
* `finrank_map_projOn_singleton_le_one`, `facet_of_singleton_witness`: for a one-species face
  the projection is *exactly* a line, so the facet hypothesis holds automatically.  Hence a
  failure of the facet hypothesis forces `2 ≤ W.card`.
* `two_le_finrank_map_projOn_of_not_facet`, `two_le_card_of_not_facet`,
  `highCodimension_of_not_facet`: the packaged dichotomy, in the network form used by
  `CRNT.Dynamics.GlobalAttractorTheorem`.  The coordinate witness is supplied by a positive
  reference point compatible with a point of the face: `w - x₀` is a stoichiometric
  displacement whose value at any `s ∈ W` is `-x₀ s ≠ 0`.

Nothing here is an axiom or a `sorry`.

Depends on: `CRNT.Dynamics.FacetRepulsionAndersonShiu`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### Rank--nullity in the degenerate direction -/

/-- **Codimension zero kills the projection.**  If the `W`-projection restricted to `U` has a
kernel of the full dimension of `U`, then its image is the zero subspace. -/
theorem map_projOn_eq_bot_of_ker_finrank_eq {W : Finset S} (U : Submodule ℝ (S → ℝ))
    (h : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict U))
        = Module.finrank ℝ U) :
    U.map (projOn W) = ⊥ := by
  have hrn := LinearMap.finrank_range_add_finrank_ker ((projOn W).domRestrict U)
  rw [LinearMap.range_domRestrict] at hrn
  have hzero : Module.finrank ℝ (U.map (projOn W)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hzero

/-- Pointwise form of `map_projOn_eq_bot_of_ker_finrank_eq`: in the codimension-zero case every
element of `U` vanishes at every species of `W`. -/
theorem eq_zero_of_mem_of_ker_finrank_eq {W : Finset S} (U : Submodule ℝ (S → ℝ))
    (h : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict U))
        = Module.finrank ℝ U)
    {p : S → ℝ} (hp : p ∈ U) {s : S} (hs : s ∈ W) : p s = 0 := by
  have hbot := map_projOn_eq_bot_of_ker_finrank_eq U h
  have hmem : projOn W p ∈ U.map (projOn W) := Submodule.mem_map_of_mem hp
  rw [hbot, Submodule.mem_bot] at hmem
  have hval := congrFun hmem s
  simpa [projOn_apply, hs] using hval

/-- **One nonvanishing coordinate makes the projection at least a line.** -/
theorem one_le_finrank_map_projOn {W : Finset S} (U : Submodule ℝ (S → ℝ))
    {p : S → ℝ} (hp : p ∈ U) {s : S} (hs : s ∈ W) (hps : p s ≠ 0) :
    1 ≤ Module.finrank ℝ (U.map (projOn W)) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ (U.map (projOn W))) with h | h
  · exfalso
    have hbot : U.map (projOn W) = ⊥ := Submodule.finrank_eq_zero.mp h
    have hmem : projOn W p ∈ U.map (projOn W) := Submodule.mem_map_of_mem hp
    rw [hbot, Submodule.mem_bot] at hmem
    have hval := congrFun hmem s
    exact hps (by simpa [projOn_apply, hs] using hval)
  · exact h

/-! ### One-species faces are always facets -/

omit [Fintype S] in
/-- The projection onto a single species has at most a one-dimensional image. -/
theorem finrank_map_projOn_singleton_le_one (U : Submodule ℝ (S → ℝ)) (s : S) :
    Module.finrank ℝ (U.map (projOn ({s} : Finset S))) ≤ 1 := by
  have hne : (Pi.single s 1 : S → ℝ) ≠ 0 := by
    intro hz
    have hval := congrFun hz s
    simp at hval
  have hle : U.map (projOn ({s} : Finset S)) ≤ Submodule.span ℝ {(Pi.single s 1 : S → ℝ)} := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
    refine Submodule.mem_span_singleton.mpr ⟨p s, ?_⟩
    funext t
    by_cases ht : t = s
    · subst ht; simp [projOn_apply]
    · simp [projOn_apply, ht]
  calc Module.finrank ℝ (U.map (projOn ({s} : Finset S)))
      ≤ Module.finrank ℝ (Submodule.span ℝ {(Pi.single s 1 : S → ℝ)}) :=
        Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hne

/-- **A one-species face with a nonvanishing witness is a facet.**  The facet dimension count of
`CRNT.Dynamics.FacetRepulsionAndersonShiu` holds automatically for `W = {s}`. -/
theorem facet_of_singleton_witness (U : Submodule ℝ (S → ℝ)) {s : S}
    {p : S → ℝ} (hp : p ∈ U) (hps : p s ≠ 0) :
    Module.finrank ℝ (LinearMap.ker ((projOn ({s} : Finset S)).domRestrict U)) + 1
      = Module.finrank ℝ U := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((projOn ({s} : Finset S)).domRestrict U)
  rw [LinearMap.range_domRestrict] at hrn
  have hlo : 1 ≤ Module.finrank ℝ (U.map (projOn ({s} : Finset S))) :=
    one_le_finrank_map_projOn U hp (Finset.mem_singleton_self s) hps
  have hhi := finrank_map_projOn_singleton_le_one U s
  omega

/-! ### The dichotomy: a failed facet count means codimension at least two -/

/-- If the facet dimension count fails while some element of `U` is nonzero somewhere on `W`,
then the `W`-projection of `U` has dimension at least two. -/
theorem two_le_finrank_map_projOn_of_not_facet {W : Finset S} (U : Submodule ℝ (S → ℝ))
    {p : S → ℝ} (hp : p ∈ U) {s : S} (hs : s ∈ W) (hps : p s ≠ 0)
    (hnot : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict U)) + 1
        ≠ Module.finrank ℝ U) :
    2 ≤ Module.finrank ℝ (U.map (projOn W)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker ((projOn W).domRestrict U)
  rw [LinearMap.range_domRestrict] at hrn
  have hlo : 1 ≤ Module.finrank ℝ (U.map (projOn W)) :=
    one_le_finrank_map_projOn U hp hs hps
  omega

/-- If the facet dimension count fails while some element of `U` is nonzero somewhere on `W`,
then `W` contains at least two species. -/
theorem two_le_card_of_not_facet {W : Finset S} (U : Submodule ℝ (S → ℝ))
    {p : S → ℝ} (hp : p ∈ U) {s : S} (hs : s ∈ W) (hps : p s ≠ 0)
    (hnot : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict U)) + 1
        ≠ Module.finrank ℝ U) :
    2 ≤ W.card := by
  by_contra hcard
  have hle : W.card ≤ 1 := by omega
  have hsingle : W = {s} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hs, ?_⟩
    intro t ht
    exact Finset.card_le_one.mp hle t ht s hs
  subst hsingle
  exact hnot (facet_of_singleton_witness U hp hps)

/-! ### Network form: the witness comes from a positive compatible reference point -/

/-- A positive reference point compatible with a point of the coordinate face supplies the
nonvanishing coordinate witness: `w - x₀` is a stoichiometric displacement taking the value
`-x₀ s ≠ 0` at every `s` of the face. -/
theorem stoich_witness_of_face_point (N : Network S)
    {x₀ w : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ w) {s : S} (hzs : w s = 0) :
    (w - x₀ : Concentration S) ∈ N.stoichSubspace ∧ (w - x₀ : Concentration S) s ≠ 0 := by
  refine ⟨hcompat, ?_⟩
  have hval : (w - x₀ : Concentration S) s = -x₀ s := by
    simp [Pi.sub_apply, hzs]
  rw [hval]
  exact neg_ne_zero.mpr (ne_of_gt (hx₀ s))

/-- **The high-codimension dichotomy for the Global Attractor Theorem.**  Let `W` be a nonempty
coordinate face met by a point `w` that is stoichiometrically compatible with a positive `x₀`.
If the Anderson--Shiu facet dimension count fails for `W`, then the failure is not degenerate:
the `W`-projection of the stoichiometric subspace has dimension at least two, and `W` contains
at least two species.

In particular the codimension-zero failure is impossible, because every stoichiometric
displacement would then vanish on `W`, forcing `w s = x₀ s > 0` against `w s = 0`. -/
theorem highCodimension_of_not_facet (N : Network S) {W : Finset S}
    {x₀ w : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ w) (hzW : ∀ s ∈ W, w s = 0) (hWne : W.Nonempty)
    (hnot : Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict N.stoichSubspace)) + 1
        ≠ Module.finrank ℝ N.stoichSubspace) :
    2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn W)) ∧ 2 ≤ W.card := by
  obtain ⟨s, hs⟩ := hWne
  obtain ⟨hmem, hne⟩ := N.stoich_witness_of_face_point hx₀ hcompat (hzW s hs)
  exact ⟨two_le_finrank_map_projOn_of_not_facet N.stoichSubspace hmem hs hne hnot,
    two_le_card_of_not_facet N.stoichSubspace hmem hs hne hnot⟩

/-- Contrapositive packaging: the codimension-zero case of a failed facet count cannot occur for
a face met by a point compatible with a positive reference point. -/
theorem ker_finrank_ne_of_face_point (N : Network S) {W : Finset S}
    {x₀ w : Concentration S} (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible x₀ w) (hzW : ∀ s ∈ W, w s = 0) (hWne : W.Nonempty) :
    Module.finrank ℝ (LinearMap.ker ((projOn W).domRestrict N.stoichSubspace))
      ≠ Module.finrank ℝ N.stoichSubspace := by
  intro hEq
  obtain ⟨s, hs⟩ := hWne
  obtain ⟨hmem, hne⟩ := N.stoich_witness_of_face_point hx₀ hcompat (hzW s hs)
  exact hne (eq_zero_of_mem_of_ker_finrank_eq N.stoichSubspace hEq hmem hs)

end Network
end CRNT
