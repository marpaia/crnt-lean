import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic

/-!
# The Cauchy–Binet formula

For a rectangular matrix `A : Matrix (Fin m) (Fin n) R` and `B : Matrix (Fin n) (Fin m) R`
over a commutative ring `R`, the determinant of the square product `A * B` expands as a sum
over the `m`-element subsets `S` of the inner index set `Fin n`:
`det (A * B) = ∑ S, det (A.submatrix id e_S) * det (B.submatrix e_S id)`,
where `e_S : Fin m → Fin n` is the strictly increasing enumeration of `S`
(`Finset.orderEmbOfFin`) and the sum ranges over `S ∈ (Finset.univ).powersetCard m`.

The identity is classical and named after Augustin-Louis Cauchy and Jacques Philippe Marie
Binet; see for instance Roger A. Horn and Charles R. Johnson, "Matrix Analysis"
(2nd ed.), §0.8.7. When `m = n` it specialises to the multiplicativity of the determinant;
when `m > n` every term vanishes and so does `det (A * B)`.

The proof mirrors Mathlib's `Matrix.det_mul`: the Leibniz expansion of `det (A * B)` becomes
a double sum over a function `p : Fin m → Fin n` and a permutation `σ`. Non-injective `p`
contribute zero by the same swap-involution argument as `Matrix.det_mul_aux`. Each injective
`p` factors uniquely as the increasing enumeration of its image followed by a permutation of
`Fin m`, which regroups the surviving terms into one block per `m`-subset `S`, each block
being `det (A.submatrix id e_S) * det (B.submatrix e_S id)`.

* `Matrix.permOfInjective` — the permutation of `Fin m` carrying the increasing enumeration of
  the image of an injective `p : Fin m → Fin n` to `p` itself.
* `Matrix.det_mul_eq_sum_powersetCard` — the Cauchy–Binet formula.

Depends on:
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, `Mathlib.Data.Finset.Sort`,
`Mathlib.Order.Fin.Basic`.
-/

namespace Matrix

open Equiv Equiv.Perm Finset Function

variable {m n : ℕ}
variable {R : Type*} [CommRing R]

local notation "ε " σ:arg => ((sign σ : ℤ) : R)

/-- For an injective `p : Fin m → Fin n`, the permutation of `Fin m` that conjugates the
increasing enumeration `(image p univ).orderEmbOfFin` of the image of `p` into `p` itself. -/
noncomputable def permOfInjective (p : Fin m → Fin n) (hp : Injective p) : Perm (Fin m) :=
  let S := Finset.image p Finset.univ
  have hS : S.card = m := by
    rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
  let eqP : Fin m ≃ {x // x ∈ S} := (Equiv.ofInjective p hp).trans
    (Set.equivOfEq (by ext x; simp [S, Set.range]))
  let eqE : Fin m ≃ {x // x ∈ S} := (S.orderIsoOfFin hS).toEquiv
  eqP.trans eqE.symm

/-- `Finset.orderEmbOfFin` only depends on the underlying finset, not on the cardinality
proof used to typecheck it. -/
theorem orderEmbOfFin_congr {S T : Finset (Fin n)} (h : S = T) {k : ℕ}
    (hS : S.card = k) (hT : T.card = k) (i : Fin k) :
    S.orderEmbOfFin hS i = T.orderEmbOfFin hT i := by
  subst h; rfl

/-- The increasing enumeration of the image of an injective `p`, reindexed by
`permOfInjective p hp`, recovers `p`. -/
theorem orderEmbOfFin_permOfInjective (p : Fin m → Fin n) (hp : Injective p) (i : Fin m)
    (hS : (Finset.image p Finset.univ).card = m) :
    (Finset.image p Finset.univ).orderEmbOfFin hS (permOfInjective p hp i) = p i := by
  rw [← Finset.coe_orderIsoOfFin_apply _ hS]
  show ↑((Finset.image p Finset.univ).orderIsoOfFin hS
    (((Finset.image p Finset.univ).orderIsoOfFin _).symm _)) = p i
  rw [OrderIso.apply_symm_apply]
  simp only [Equiv.trans_apply, Equiv.ofInjective_apply]
  rfl

/-- The swap-involution cancellation: for a non-injective column-selecting function `p`, the
signed Leibniz block sums to zero, exactly as in `Matrix.det_mul_aux`. -/
theorem cauchyBinet_aux (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    {p : Fin m → Fin n} (H : ¬ Function.Injective p) :
    (∑ σ : Perm (Fin m), ε σ * ∏ x, A (σ x) (p x) * B (p x) x) = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    rw [Injective] at H
    push Not at H
    exact H
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, A (σ x) (p x)) = ∏ x, A ((σ * Equiv.swap i j) x) (p x) :=
          Fintype.prod_equiv (swap i j) _ _ (by simp [apply_swap_eq_self hpij])
        simp [this, sign_swap hij, -sign_swap', prod_mul_distrib])
      (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _) fun σ _ =>
      mul_swap_involutive i j σ

/-- A single Cauchy–Binet block, for square matrices `M N`: the double sum over a column
permutation `τ` and a row permutation `σ` of the signed Leibniz terms equals the product of
determinants. This is the tail of Mathlib's `Matrix.det_mul`. -/
theorem cauchyBinet_block (M N : Matrix (Fin m) (Fin m) R) :
    (∑ τ : Perm (Fin m), ∑ σ : Perm (Fin m), ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i)
      = M.det * N.det := by
  calc
    (∑ τ : Perm (Fin m), ∑ σ : Perm (Fin m), ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i)
        = ∑ σ : Perm (Fin m), ∑ τ : Perm (Fin m),
            (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
          simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
    _ = ∑ σ : Perm (Fin m), ∑ τ : Perm (Fin m),
          (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
        (sum_congr rfl fun σ _ =>
          Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun τ => by
            have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
              rw [← (σ⁻¹ : _ ≃ _).prod_comp]
              simp
            have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
              calc
                ε σ * ε (τ * σ⁻¹) = ε (τ * σ⁻¹ * σ) := by
                  rw [mul_comm, sign_mul (τ * σ⁻¹)]
                  simp only [Int.cast_mul, Units.val_mul]
                _ = ε τ := by simp only [inv_mul_cancel_right]
            simp_rw [Equiv.coe_mulRight, h]
            simp only [this])
    _ = M.det * N.det := by
        simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- **The Cauchy–Binet formula.** The determinant of the product of a rectangular matrix
`A : Matrix (Fin m) (Fin n) R` and `B : Matrix (Fin n) (Fin m) R` is the sum, over the
`m`-element subsets `S` of the inner index set `Fin n`, of the product of the corresponding
`m × m` minors of `A` and `B`. The increasing enumeration of `S` is `Finset.orderEmbOfFin`,
and the sum is taken over `(Finset.univ).powersetCard m` (the membership proof `S.2` supplies
`S.1.card = m`). -/
theorem det_mul_eq_sum_powersetCard (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).attach,
      (A.submatrix id (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2)).det *
        (B.submatrix (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2) id).det := by
  have leibniz : (A * B).det = ∑ p : Fin m → Fin n, ∑ σ : Perm (Fin m),
      ε σ * ∏ i, A (σ i) (p i) * B (p i) i := by
    simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
    rw [Finset.sum_comm]
  rw [leibniz]
  -- Restrict the sum over all `p` to injective `p`.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (Function.Injective ·)]
  have hzero : (∑ p ∈ Finset.univ.filter (¬ Function.Injective ·),
      ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i) * B (p i) i) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    exact cauchyBinet_aux A B (Finset.mem_filter.mp hp).2
  rw [hzero, add_zero]
  -- Reindex injective `p` by `(S, τ)` and split the product over the attached subset finset.
  rw [show (∑ p ∈ Finset.univ.filter (Function.Injective ·),
        ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i) * B (p i) i)
      = ∑ Sτ ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).attach ×ˢ
            (Finset.univ : Finset (Perm (Fin m))),
          ∑ σ : Perm (Fin m), ε σ * ∏ i,
            A (σ i) (Sτ.1.1.orderEmbOfFin (Finset.mem_powersetCard.mp Sτ.1.2).2 (Sτ.2 i)) *
            B (Sτ.1.1.orderEmbOfFin (Finset.mem_powersetCard.mp Sτ.1.2).2 (Sτ.2 i)) i from ?_]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← cauchyBinet_block (A.submatrix id (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2))
      (B.submatrix (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2) id)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine Finset.sum_congr rfl fun σ _ => ?_
    rfl
  -- The reindexing bijection.
  refine Finset.sum_bij'
    (fun p hp => (⟨Finset.image p Finset.univ, by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, by
          rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hp).2,
            Finset.card_univ, Fintype.card_fin]⟩⟩,
        permOfInjective p (Finset.mem_filter.mp hp).2))
    (fun Sτ _ => Sτ.1.1.orderEmbOfFin (Finset.mem_powersetCard.mp Sτ.1.2).2 ∘ Sτ.2)
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product]
    exact ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩
  · intro Sτ _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (Sτ.1.1.orderEmbOfFin _).injective.comp Sτ.2.injective⟩
  · intro p hp
    funext i
    exact orderEmbOfFin_permOfInjective p (Finset.mem_filter.mp hp).2 i _
  · intro Sτ _
    obtain ⟨⟨S, hSmem⟩, τ⟩ := Sτ
    have hScard : S.card = m := (Finset.mem_powersetCard.mp hSmem).2
    have hq : Function.Injective (S.orderEmbOfFin hScard ∘ τ) :=
      (S.orderEmbOfFin hScard).injective.comp τ.injective
    have himg : Finset.image (S.orderEmbOfFin hScard ∘ τ) Finset.univ = S := by
      rw [Finset.image_comp, Finset.image_univ_of_surjective τ.surjective,
        Finset.image_orderEmbOfFin_univ]
    refine Prod.ext (Subtype.ext himg) ?_
    dsimp only
    apply Equiv.ext
    intro i
    have key := orderEmbOfFin_permOfInjective (S.orderEmbOfFin hScard ∘ τ) hq i
      (by rw [Finset.card_image_of_injective _ hq, Finset.card_univ, Fintype.card_fin])
    apply (S.orderEmbOfFin hScard).injective
    rw [Function.comp_apply] at key
    rw [← key]
    exact orderEmbOfFin_congr himg.symm _ _ _
  · intro p hp
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [orderEmbOfFin_permOfInjective p (Finset.mem_filter.mp hp).2 i]

end Matrix
