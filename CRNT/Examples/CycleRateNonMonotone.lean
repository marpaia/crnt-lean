import CRNT.Dynamics.ToricEmbeddingWR

/-!
# A weakly reversible cycle whose mass-action rates admit no monotone rotation

`NetworkCycleDecomposition` (`CRNT.Dynamics.ToricEmbeddingWR`) asks each cycle for two things at
once:

* `mono : Monotone (a j)` — the coefficients, pinned by `coeff` to the mass-action rates of the
  chosen reactions, increase along the cycle;
* `cmin : CMinimal C (u j)` — the base vertex minimises `⟪z, ·⟫` over the walk for every `z ∈ C`,
  where `vec` pins `u j (i+1) - u j i` to the reaction vector of `e j i`.

For a *graph* cycle (consecutive reactions, so `u j i` is the `i`-th source complex) `mono` says the
mass-action rates are nondecreasing all the way round. That is not a property one can arrange by
choosing where to start: this module exhibits a strongly connected three-reaction network and a
positive state at which the three cyclic rates are `1/2, 4, 2`, and **no rotation of that cyclic
order is monotone**.

The escape hatch — reordering the reactions arbitrarily, which is permitted because `vec` only
constrains consecutive *differences* and the reaction vectors sum to zero — sorts the rates and so
satisfies `mono`, but it destroys the identification of `u j i` with the source complexes, and with
it the route to `cmin`. Under that reordering the vertices are partial sums of reaction vectors in
rate order, and their `C`-minimality is no longer supplied by anything.

So item 3 of the toric route (`docs/persistence-gac.md`) is not merely unproven: the interface needs
restating before a cycle cover can feed it. Either `mono` must be weakened to monotone *runs* with
explicit descent corrections, or `cmin` must be established for the sorted partial-sum walk.

The network is the directed triangle on complexes `A → B → A + B → A`, whose reaction vectors
`(-1,1)`, `(1,0)`, `(0,-1)` sum to zero. It is strongly connected, hence weakly reversible.
-/

namespace CRNT.Network

open scoped BigOperators

/-- `r₀ : A → B`, `r₁ : B → A + B`, `r₂ : A + B → A`. -/
private abbrev triN : Network (Fin 2) where
  R := Fin 3
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := fun s => if s = 0 then 1 else 0
        target := fun s => if s = 0 then 0 else 1 }
    else if r = 1 then
      { source := fun s => if s = 0 then 0 else 1
        target := fun _ => 1 }
    else
      { source := fun _ => 1
        target := fun s => if s = 0 then 1 else 0 }

private def triK : triN.RateConstants where
  k := fun _ => 1
  positive := fun _ => one_pos

/-- The positive state `x = (1/2, 4)`. -/
private noncomputable def triX : Concentration (Fin 2) :=
  fun s => if s = 0 then 1 / 2 else 4

private theorem triX_positive : Concentration.Positive triX := by
  intro s
  by_cases h : s = 0 <;> simp [triX, h]

/-! ### The reaction vectors sum to zero, so the triangle is a closed walk -/

private theorem tri_reactionVector_sum_zero :
    triN.reactionVector 0 + triN.reactionVector 1 + triN.reactionVector 2 = 0 := by
  funext s
  by_cases h : s = 0 <;>
    simp [Network.reactionVector, h]

/-! ### The three cyclic mass-action rates are `1/2`, `4`, `2` -/

private theorem rate_zero : triN.massActionRate triK 0 triX = 1 / 2 := by
  simp [Network.massActionRate, Complex.massActionMonomial, triK, triX]

private theorem rate_one : triN.massActionRate triK 1 triX = 4 := by
  simp [Network.massActionRate, Complex.massActionMonomial, triK, triX, Fin.prod_univ_two]

private theorem rate_two : triN.massActionRate triK 2 triX = 2 := by
  simp [Network.massActionRate, Complex.massActionMonomial, triK, triX, Fin.prod_univ_two]
  norm_num

/-- **No rotation of the cyclic rate sequence is monotone.**  The three rotations of
`(1/2, 4, 2)` are `(1/2, 4, 2)`, `(4, 2, 1/2)` and `(2, 1/2, 4)`; none is nondecreasing.  Hence no
`NetworkCycleDecomposition` cycle can traverse this triangle in graph order and satisfy `mono`. -/
theorem tri_no_monotone_rotation :
    ¬ (triN.massActionRate triK 0 triX ≤ triN.massActionRate triK 1 triX ∧
        triN.massActionRate triK 1 triX ≤ triN.massActionRate triK 2 triX) ∧
    ¬ (triN.massActionRate triK 1 triX ≤ triN.massActionRate triK 2 triX ∧
        triN.massActionRate triK 2 triX ≤ triN.massActionRate triK 0 triX) ∧
    ¬ (triN.massActionRate triK 2 triX ≤ triN.massActionRate triK 0 triX ∧
        triN.massActionRate triK 0 triX ≤ triN.massActionRate triK 1 triX) := by
  rw [rate_zero, rate_one, rate_two]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, h2⟩
    norm_num at h2
  · rintro ⟨h1, -⟩
    norm_num at h1
  · rintro ⟨h1, -⟩
    norm_num at h1

end CRNT.Network
