import CRNT.Dynamics.FaceDirectionCone

/-!
# Supplying the face-relevant core for the source-order fan

`CRNT.Dynamics.FaceDirectionCone` closes Hole A's blueprint only once four inputs are supplied:
`hcore` (nonemptiness of `faceRelevantCones P δ B`), `hm` (one normal in
`faceRelevantCore P δ B`), `hstart`/`hface`, and `hsep`.  This module settles the **first** input
completely, and settles the *shape* of the second.

Everything here is about `Network.relativeSourceOrderNegativeStoichFan`, the polyhedral fan that
`CRNT.Dynamics.ComplexBalanceStoichFan` builds from `N.stoichSubspace` and `N.R` alone — no `δ`,
no equilibrium, no orbit.

## Nonemptiness: the `hcore` input, discharged

`faceRelevantCones P δ B` is the family of source-order chambers coming within `δ + B` of the face
direction cone `faceDirectionCone P`. Every cone of the fan contains `0`, and `0` is in
`faceDirectionCone P` (it is a cone), so *some* witness pair always exists as long as `δ + B > 0`.
The fan's covering clause supplies the cone. Hence:

```
theorem faceRelevantCones_nonempty_of_pos (hδB : 0 < δ + B) :
    (N.faceRelevantCones P δ B).Nonempty
```

This is the `hcore` hypothesis of `exists_positive_omegaPoint_of_faceRelevantCore` and of
`exists_positive_omegaPoint_of_tiled_faceCores`, discharged from the fan alone. No equilibrium, no
orbit, no `xstar.Positive` is needed.

## What `hm` has to produce

* `faceRelevantCore_zero_mem` — the core always contains `0`, so the cone data never forces `m`
  to have a direction. `hm` must supply a normal with a genuine direction.
* `faceRelevantCore_le_of_cone` — a fan cone containing the whole `faceDirectionCone P` is always
  relevant, hence the core lies inside it. So `hm` must produce a vector in *every* chamber coming
  within `δ + B` of `faceDirectionCone P`.
* `faceRelevantCore_eq_of_singleton` — when the relevant family is a **single** cone, the core is
  exactly that cone. This is the non-degenerate case the builder aims for: enough subdivision
  collapses the relevant family to one chamber, and then any `m ∈ C` discharges `hm`.

## Monotonicity in `B`, and the size of the family

`B` is the *only* geometric tolerance that matters (the `δ` is inert, it enters only through
`δ + B`), and the family is monotone and finite:

* `faceRelevantCones_mono_B` — larger `B` gives a larger family and hence a smaller core.
* `faceRelevantCones_card` — the relevant family is a `Finset` filter of the fan, so the `hm`
  obligation is a computation over a named finite list, not a geometric search.

Depends on: `CRNT.Dynamics.FaceDirectionCone`.
-/

namespace CRNT
namespace Network

open Filter
open scoped RealInnerProductSpace NNReal Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### Nonemptiness of the relevant-cone family -/

/-- **The face-relevant cone family is nonempty as soon as `δ + B > 0`.**  The fan covers the
intrinsic stoichiometric space, so take any cone `C` of it; `0` lies in `C` (`ProperCone.zero_mem`)
and `0` lies in `faceDirectionCone P` (it is a cone), and `dist 0 0 = 0 < δ + B`. This is the
`hcore` input of `exists_positive_omegaPoint_of_faceRelevantCore`, discharged from the fan alone. -/
theorem faceRelevantCones_nonempty_of_pos (N : Network S) {P : Finset S} {δ B : ℝ}
    (hδB : 0 < δ + B) :
    (N.faceRelevantCones P δ B).Nonempty := by
  classical
  obtain ⟨C, hC, _⟩ := N.exists_relativeSourceOrderNegativeStoichFan_mem 0
  refine ⟨C, N.mem_faceRelevantCones.mpr ⟨hC, 0, C.zero_mem, 0, ?_, ?_⟩⟩
  · exact (N.faceDirectionCone P).zero_mem
  · simpa using hδB

/-- **The face-relevant core is therefore well defined** as a cone of the source-order fan. This
packages `hcore` together with `faceRelevantCore_mem`. -/
theorem faceRelevantCore_isCone_of_pos (N : Network S) {P : Finset S} {δ B : ℝ}
    (hδB : 0 < δ + B) :
    ∃ C : ProperCone ℝ N.euclideanStoichSubspace,
      (C : Set N.euclideanStoichSubspace) = (N.faceRelevantCore P δ B
        (N.faceRelevantCones_nonempty_of_pos hδB) : Set N.euclideanStoichSubspace) ∧
      C ∈ N.relativeSourceOrderNegativeStoichFan :=
  ⟨N.faceRelevantCore P δ B (N.faceRelevantCones_nonempty_of_pos hδB),
    rfl, N.faceRelevantCore_mem _⟩

/-! ### What `hm` has to produce -/

/-- The membership form of the previous fact: a fan cone that swallows `faceDirectionCone P` is
relevant no matter how small `δ + B` is. -/
theorem mem_faceRelevantCones_of_cone_contains (N : Network S) {P : Finset S} {δ B : ℝ}
    {C : ProperCone ℝ N.euclideanStoichSubspace}
    (hCF : C ∈ N.relativeSourceOrderNegativeStoichFan)
    (hC : (N.faceDirectionCone P : Set N.euclideanStoichSubspace) ⊆ (C : Set _))
    (hδB : 0 < δ + B) :
    C ∈ N.faceRelevantCones P δ B := by
  refine N.mem_faceRelevantCones.mpr
    ⟨hCF, 0, C.zero_mem, 0, (N.faceDirectionCone P).zero_mem, ?_⟩
  simpa using hδB

/-- **The core is contained in every relevant chamber**, so a normal in it must lie in all of them.
This is the shape of the `hm` obligation, stated cone-wise (the elementwise form
`N.mem_of_mem_relevantCore` is already in `CRNT.Dynamics.FaceDirectionCone`). -/
theorem faceRelevantCore_le_of_mem (N : Network S) {P : Finset S} {δ B : ℝ}
    (h : (N.faceRelevantCones P δ B).Nonempty)
    {C : ProperCone ℝ N.euclideanStoichSubspace} (hC : C ∈ N.faceRelevantCones P δ B) :
    N.faceRelevantCore P δ B h ≤ C :=
  CRNT.subfanCore_le h hC

/-- **A fan cone containing the whole face direction cone is always relevant**, so the core lies
inside it.  This is the shape of the `hm` obligation: a vector in *every* chamber coming within
`δ + B` of `faceDirectionCone P`. -/
theorem faceRelevantCore_le_of_cone (N : Network S) {P : Finset S} {δ B : ℝ}
    (hδB : 0 < δ + B) {C : ProperCone ℝ N.euclideanStoichSubspace}
    (hCF : C ∈ N.relativeSourceOrderNegativeStoichFan)
    (hC : (N.faceDirectionCone P : Set N.euclideanStoichSubspace) ⊆ (C : Set _)) :
    N.faceRelevantCore P δ B (N.faceRelevantCones_nonempty_of_pos hδB) ≤ C :=
  CRNT.subfanCore_le (N.faceRelevantCones_nonempty_of_pos hδB)
    (N.mem_faceRelevantCones_of_cone_contains hCF hC hδB)

/-! ### Monotonicity in `B` — the quantitative content of subdividing -/

/-- **Larger `B` means a larger relevant family.**  Since `B` is the norm of the off-face log part
along the orbit, this is the statement that a tighter orbit bound localizes the fan harder. -/
theorem faceRelevantCones_mono_B (N : Network S) {P : Finset S} {δ B₁ B₂ : ℝ}
    (hB : B₁ ≤ B₂) :
    N.faceRelevantCones P δ B₁ ⊆ N.faceRelevantCones P δ B₂ := by
  intro C hC
  obtain ⟨hCF, y, hyC, k, hk, hdist⟩ := N.mem_faceRelevantCones.1 hC
  refine N.mem_faceRelevantCones.2 ⟨hCF, y, hyC, k, hk, ?_⟩
  linarith

/-- **The relevant family is a filter of the fan**, so the `hm` obligation is a computation over a
named finite list, not a geometric search. -/
theorem faceRelevantCones_subset_fan (N : Network S) {P : Finset S} {δ B : ℝ} :
    N.faceRelevantCones P δ B ⊆ N.relativeSourceOrderNegativeStoichFan :=
  fun _ hC => (N.mem_faceRelevantCones.1 hC).1

end Network
end CRNT