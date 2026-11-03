import CRNT.Equilibria.NilpotentJacobian
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Equilibria.MatrixTreeCofactorDefs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The spectral form of the Horn--Jackson argument

This module formalizes the **spectral form** of the classical argument behind the
nilpotent-Jacobian criterion of field-map leaf **S20**
(`CRNT.Equilibria.NilpotentJacobian`).

## What the classical argument says

For a mass-action network `N` with rate constants `κ` the vector field factorises
(`CRNT.Dynamics.MassActionAlgebra`) as

```text
ẋ = Y (A_κ Ψ x)
```

with `Y` the *complex matrix* (species against complexes), `A_κ` the *kinetic* matrix of the
reaction graph and `Ψ` the monomial map.  Differentiating at a point `x` where the kinetic
map kills the monomial vector (`A_κ Ψ x = 0`, i.e. `x` is complex balanced) leaves

```text
J(x) = Y A_κ diag(Ψ x) Yᵀ D(x)⁻¹ ,
```

the **spectral factorization** of the mass-action Jacobian proved below as
`CRNT.Network.massActionJacobian_eq_factorization`.  The right-hand side is a product of
the *kinetic operator* with the *scaled complex Gram matrix* `Y D(x)⁻¹ Yᵀ`; the classical
statement that "the spectrum of the Jacobian is the spectrum of the kinetic matrix" is
therefore the Sylvester identity `AB` versus `BA`, which Mathlib provides as
`Matrix.charpoly_mul_comm'`:

```text
X^|complexes| · charpoly J  =  X^|species| · charpoly M ,
```

with `M = A_κ diag(Ψ x) Y D(x)⁻¹ Yᵀ` the **complex-space operator**
(`CRNT.Network.complexSpaceOperator`).  In particular, when the network has as many
complexes as species the two characteristic polynomials agree
(`CRNT.Network.charpoly_massActionJacobian_eq_charpoly_complexSpaceOperator`), and in
all cases the traces agree
(`CRNT.Network.trace_massActionJacobian_eq_trace_complexSpaceOperator`).

## A remark on the naive form of the statement

The often-quoted slogan "the eigenvalues of the Jacobian at a complex-balanced equilibrium
are the negatives of the eigenvalues of the weighted adjacency matrix" is **not** correct as
stated, for two reasons that this module makes explicit.

* The mass-action Jacobian is an `|S| × |S|` matrix on *species*, while the weighted
  adjacency matrix is an `|N.ComplexIdx| × |N.ComplexIdx|` matrix on *complexes*: the two
  matrices generally have different sizes, so their characteristic polynomials cannot be
  compared term by term.  The correct comparison is the Sylvester identity above, which
  compares the characteristic polynomials up to a power of `X`.
* Even in the equal-size case the comparison is not with the bare weighted adjacency matrix
  `A_κ`: the scaling by `D(x*)⁻¹` (and the Gram matrix `Yᵀ Y`) cannot be dropped.  For the
  network `A ⇄ B` with rates `1` and `2` (the instance checked numerically below) the
  complex-balanced equilibrium is `x* = (2, 1)`, the Jacobian is `[[-1, 2], [1, -2]]` with
  characteristic polynomial `X^2 + 3X`, whereas the monomial-weighted adjacency matrix is
  `[[0, 2], [2, 0]]` with characteristic polynomial `X^2 - 4`: the two spectra differ, so
  the slogan fails even when the two matrices have the same size.  Likewise, for the network
  `A ⇄ 2A` with rates `k₁ = 2`, `k₂ = 1` the complex-balanced equilibrium is `x* = 2`, the
  Jacobian is `[-2]` while the monomial-weighted adjacency matrix is `[[0, 4], [4, 0]]`, whose
  eigenvalues are `±4`; the spectral partner of the Jacobian is the complex-space operator
  `[[2, 4], [-2, -4]]`, whose eigenvalues are `0` and `-2`, as the Sylvester identity
  demands.

What *is* true, and what the classical argument uses, is the following chain, all of it
proved here:

* the **monomial-weighted adjacency matrix** `N.weightedAdjacencyMatrix` (the `(c, d)` entry
  is the sum of the rate constants of the reactions from `d` to `c`, weighted by the
  monomial of the source complex) is entrywise nonnegative at a positive concentration
  (`CRNT.Network.weightedAdjacencyMatrix_nonneg`);
* the **monomial-weighted kinetic Laplacian** `N.weightedKineticLaplacian` (the weighted
  adjacency minus the weighted outflow) annihilates the all-ones vector at a
  complex-balanced equilibrium — the generalized complex balance of Shinohara
  (`CRNT.Network.weightedKineticLaplacian_mulVec_one_eq_zero_of_complexBalanced`);
* the Jacobian at a complex-balanced equilibrium annihilates the (scaled) conservation
  laws (`CRNT.Network.massActionJacobian_mulVec_conservationLaw_eq_zero`);
* the **spectral nilpotent criterion**: the mass-action Jacobian is nilpotent at `x*` if
  and only if the complex-space operator is nilpotent, i.e. if and only if all its
  eigenvalues vanish
  (`CRNT.Network.isNilpotent_massActionJacobian_iff_isNilpotent_complexSpaceOperator`,
  `CRNT.Network.charpoly_complexSpaceOperator_eq_X_pow_of_isNilpotent_jacobian`);
* the **Perron--Frobenius step**: an entrywise nonnegative matrix that has a strictly
  positive power is not nilpotent
  (`CRNT.Network.not_isNilpotent_of_nonneg_of_pos_mulVec`,
  `CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_pos_mulVec`), the classical
  ingredient that turns nilpotency of the kinetic data into triviality of the network: a
  nonnegative matrix whose support digraph is strongly connected (so that some power is
  strictly positive) cannot be nilpotent.

## The instances

`CRNT.Examples.JacobianSpectrum` checks the spectral identity numerically for the network
`A ⇄ B` with rates `1` and `2`: at the complex-balanced equilibrium `x* = (2, 1)` the
mass-action Jacobian is `[[-1, 2], [1, -2]]` and its characteristic polynomial is
`X^2 + 3X`.  `CRNT.Examples.NilpotentJacobian` checks the nilpotent case: for the self-loop
network `A → A` the Jacobian is the zero matrix, its characteristic polynomial is `X`, and the
complex-space operator is nilpotent.

The entropy-metric form of the same classical argument (the Horn--Jackson sum-of-squares
identity) is `CRNT.Network.complexBalanceJacobianQuadratic_eq_neg_sum_sq` and is used in
`CRNT.Equilibria.NilpotentJacobian`; this module adds the spectral counterpart.

Depends on: `CRNT.Equilibria.NilpotentJacobian`, `CRNT.Dynamics.MassActionAlgebra`,
`CRNT.Equilibria.MatrixTreeCofactorDefs`, Mathlib `Matrix.Charpoly.Coeff`,
`Matrix.Trace`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The complex matrix -/

/-- The **complex matrix** `Y` of the network: its rows are indexed by the complexes of the
network and its columns by the species; the entry `(c, s)` is the stoichiometric coefficient
of the species `s` in the complex `c`.  This is the matrix of the complex map
`CRNT.Network.complexMap`. -/
noncomputable def complexSpeciesMatrix (N : Network S) : Matrix N.ComplexIdx S ℝ :=
  fun c s => (c.val s : ℝ)

@[simp] theorem complexMatrix_apply (N : Network S) (c : N.ComplexIdx) (s : S) :
    N.complexSpeciesMatrix c s = (c.val s : ℝ) := rfl

/-- The action of the complex matrix on a species vector: the `c`-th entry is the pairing of
the complex `c` with the vector. -/
theorem complexMatrix_mulVec (N : Network S) (v : Concentration S) (c : N.ComplexIdx) :
    (N.complexSpeciesMatrix).mulVec v c = ∑ s : S, (c.val s : ℝ) * v s := by
  simp [Matrix.mulVec, dotProduct]

/-- The action of the transposed complex matrix on a complex vector: the `i`-th entry is the
pairing of the species `i` with the complex vector. -/
theorem complexMatrix_transpose_mulVec (N : Network S) (w : N.ComplexIdx → ℝ) (i : S) :
    (Matrix.transpose N.complexSpeciesMatrix).mulVec w i = ∑ c : N.ComplexIdx, (c.val i : ℝ) * w c := by
  simp [Matrix.mulVec, dotProduct]

/-! ## The monomial-weighted adjacency matrix -/

/-- The **monomial-weighted adjacency matrix** of the network at the concentration `x`: the
`(c, d)` entry is the sum of the rate constants of the reactions running *from* the complex
`d` *to* the complex `c`, each weighted by the mass-action monomial of its source complex.

At a positive concentration this matrix is entrywise nonnegative, which is the
Perron--Frobenius input of the classical criterion. -/
noncomputable def weightedAdjacencyMatrix (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Matrix N.ComplexIdx N.ComplexIdx ℝ :=
  fun c d => ∑ r : N.R, if N.sourceIdx r = d then
      (if N.targetIdx r = c then κ.k r * N.complexMonomialVector x (N.sourceIdx r) else 0)
    else 0

/-- The **monomial-weighted outflow matrix** at `x`: the diagonal entry at `c` is the total
weighted outflow from the complex `c`. -/
noncomputable def weightedOutflowMatrix (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Matrix N.ComplexIdx N.ComplexIdx ℝ :=
  fun c d => ∑ r : N.R, if N.sourceIdx r = d then
      (if d = c then κ.k r * N.complexMonomialVector x (N.sourceIdx r) else 0)
    else 0

/-- The **monomial-weighted kinetic Laplacian** of the network at `x`: the inflow-minus-outflow
matrix of the reaction graph, every edge weighted by the rate constant of the reaction and by
the mass-action monomial of its source complex.  This is the matrix `A_κ` of the classical
argument, evaluated at `x`. -/
noncomputable def weightedKineticLaplacian (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Matrix N.ComplexIdx N.ComplexIdx ℝ :=
  fun c d => ∑ r : N.R, if N.sourceIdx r = d then
      κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
        ((if N.targetIdx r = c then 1 else 0) - (if d = c then 1 else 0))
    else 0

/-- **Entrywise, the monomial-weighted kinetic Laplacian is the difference of the
monomial-weighted adjacency matrix and the monomial-weighted outflow matrix.** -/
theorem weightedKineticLaplacian_apply (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) (c d : N.ComplexIdx) :
    N.weightedKineticLaplacian κ x c d
      = N.weightedAdjacencyMatrix κ x c d - N.weightedOutflowMatrix κ x c d := by
  classical
  simp only [weightedKineticLaplacian, weightedAdjacencyMatrix, weightedOutflowMatrix]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hsrc : N.sourceIdx r = d
  · by_cases htgt : N.targetIdx r = c
    · by_cases hdc : d = c
      · simp only [ite_eq_left hsrc, ite_eq_left htgt, ite_eq_left hdc]
        ring
      · simp only [ite_eq_left hsrc, ite_eq_left htgt, ite_eq_right hdc]
        ring
    · by_cases hdc : d = c
      · simp only [ite_eq_left hsrc, ite_eq_right htgt, ite_eq_left hdc]
        ring
      · simp only [ite_eq_left hsrc, ite_eq_right htgt, ite_eq_right hdc]
        ring
  · simp only [ite_eq_right hsrc]
    ring

/-- The monomial-weighted adjacency matrix is entrywise nonnegative at a positive
concentration. -/
theorem weightedAdjacencyMatrix_nonneg (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (c d : N.ComplexIdx) :
    0 ≤ N.weightedAdjacencyMatrix κ x c d := by
  classical
  unfold Network.weightedAdjacencyMatrix
  refine Finset.sum_nonneg fun r _ => ?_
  by_cases hsrc : N.sourceIdx r = d
  · by_cases htgt : N.targetIdx r = c
    · simp only [ite_eq_left hsrc, ite_eq_left htgt]
      exact mul_nonneg (κ.positive r).le
        (N.complexMonomialVector_pos hx (N.sourceIdx r)).le
    · simp only [ite_eq_left hsrc, ite_eq_right htgt]
      exact le_rfl
  · simp only [ite_eq_right hsrc]
    exact le_rfl

/-- The action of the monomial-weighted kinetic Laplacian on a complex vector. -/
theorem weightedKineticLaplacian_mulVec (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (z : N.ComplexIdx → ℝ) (c : N.ComplexIdx) :
    (N.weightedKineticLaplacian κ x).mulVec z c
      = ∑ r : N.R, κ.k r * N.complexMonomialVector x (N.sourceIdx r) * z (N.sourceIdx r) *
          ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)) := by
  classical
  simp only [Network.weightedKineticLaplacian, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single (N.sourceIdx r)]
  · simp
    ring
  · intro d _ hd
    simp [ite_eq_right (Ne.symm hd)]
  · simp

/-! ## The complex-space operator -/

/-- The **scaled complex Gram matrix** at `x`: the `(c, d)` entry is the `x`-weighted inner
product of the complexes `c` and `d`, `∑ s, (c s) (d s) / x s`.  It is the matrix
`Y D(x)⁻¹ Yᵀ` of the classical argument. -/
noncomputable def complexGramMatrix (N : Network S) (x : Concentration S) :
    Matrix N.ComplexIdx N.ComplexIdx ℝ :=
  N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s) * Matrix.transpose N.complexSpeciesMatrix

/-- **Entrywise, the scaled complex Gram matrix** is the `x`-weighted inner product of the
complexes: the `(c, d)` entry is `∑ s, (c s) (d s) / x s`. -/
theorem complexGramMatrix_apply (N : Network S) (x : Concentration S) (c d : N.ComplexIdx) :
    N.complexGramMatrix x c d = ∑ s : S, (c.val s : ℝ) * (d.val s : ℝ) / x s := by
  classical
  unfold complexGramMatrix
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hinner : (∑ t : S, N.complexSpeciesMatrix c t * (if t = j then 1 / x t else 0))
      = N.complexSpeciesMatrix c j * (1 / x j) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro t _ ht
      rw [ite_eq_right ht, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [hinner]
  simp only [N.complexMatrix_apply]
  ring

/-- The **complex-space operator** of the network at `x`: the monomial-weighted kinetic
Laplacian applied to the scaled complex Gram matrix.  By the spectral identity
(`CRNT.Network.charpoly_massActionJacobian_mul_comm`) its characteristic polynomial agrees
with that of the mass-action Jacobian, up to a power of `X`. -/
noncomputable def complexSpaceOperator (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Matrix N.ComplexIdx N.ComplexIdx ℝ :=
  (N.weightedKineticLaplacian κ x *
    (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s))) * Matrix.transpose N.complexSpeciesMatrix


/-! ## The spectral factorization of the mass-action Jacobian -/

/-- The action of the diagonal matrix `D(x)⁻¹` on a species vector. -/
theorem diagonal_inv_mulVec (x : Concentration S) (h : Concentration S) (s : S) :
    (Matrix.diagonal (fun t => 1 / x t)).mulVec h s = h s / x s := by
  rw [Matrix.mulVec_diagonal]
  simp [div_eq_mul_inv, mul_comm]

/-- The pairing of a species with a complex vector, summed over the complexes: the
`i`-th coordinate of the transposed complex matrix applied to a complex vector. -/
theorem sum_mul_ite_complexIdx (N : Network S) (c₀ : N.ComplexIdx) (i : S) :
    (∑ c : N.ComplexIdx, (c.val i : ℝ) * (if c₀ = c then 1 else 0)) = (c₀.val i : ℝ) := by
  classical
  rw [Finset.sum_eq_single c₀]
  · simp
  · intro c _ hc
    rw [ite_eq_right (Ne.symm hc), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ c₀) h

/-- The reaction-vector identity in complex coordinates: the `i`-th coordinate of the
reaction vector is the pairing of the species `i` with the difference of the target and
source indicator functions on the complexes. -/
theorem sum_mul_sub_ite_complexIdx (N : Network S) (i : S) (r : N.R) :
    (∑ c : N.ComplexIdx, (c.val i : ℝ) *
        ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)))
      = ((N.reaction r).target i : ℝ) - ((N.reaction r).source i : ℝ) := by
  classical
  have hsplit : (∑ c : N.ComplexIdx, (c.val i : ℝ) *
        ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)))
      = (∑ c : N.ComplexIdx, (c.val i : ℝ) * (if N.targetIdx r = c then 1 else 0)) -
        (∑ c : N.ComplexIdx, (c.val i : ℝ) * (if N.sourceIdx r = c then 1 else 0)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hsplit, sum_mul_ite_complexIdx N (N.targetIdx r) i,
    sum_mul_ite_complexIdx N (N.sourceIdx r) i]
  rfl

/-- Distributing a constant factor over a finite sum of pairings. -/
theorem sum_mul_factor {ι : Type} [Fintype ι] (A : ℝ) (f g : ι → ℝ) :
    (∑ c : ι, f c * (A * g c)) = A * ∑ c : ι, f c * g c := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- **The spectral factorization of the mass-action Jacobian.**

At a positive concentration `x` the mass-action Jacobian factorises as the product of the
transposed complex matrix, the monomial-weighted kinetic Laplacian, the complex matrix and
the inverse diagonal matrix `D(x)⁻¹`:

```text
J(x) = Yᵀ A_κ(x) Y D(x)⁻¹ .
```

This is the classical Feinberg--Horn--Jackson linearisation of the mass-action field at a
complex-balanced equilibrium, in matrix form. -/
theorem massActionJacobian_mulVec_eq_factorization (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (h : Concentration S) :
    (N.massActionJacobian κ x).mulVec h =
      (Matrix.transpose N.complexSpeciesMatrix * (N.weightedKineticLaplacian κ x *
        (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s)))).mulVec h := by
  classical
  have hRHS : (Matrix.transpose N.complexSpeciesMatrix * (N.weightedKineticLaplacian κ x *
        (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s)))).mulVec h
      = Matrix.mulVec (Matrix.transpose N.complexSpeciesMatrix)
          (Matrix.mulVec (N.weightedKineticLaplacian κ x)
            (Matrix.mulVec N.complexSpeciesMatrix
              (Matrix.mulVec (Matrix.diagonal (fun s => 1 / x s)) h))) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hRHS]
  -- the complex-space vector `Y D(x)⁻¹ h`
  have hY : ∀ c : N.ComplexIdx,
      (Matrix.mulVec N.complexSpeciesMatrix (Matrix.mulVec (Matrix.diagonal (fun s => 1 / x s)) h)) c
        = ∑ s : S, ((c.val s : ℝ)) * (h s / x s) := by
    intro c
    rw [N.complexMatrix_mulVec]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [diagonal_inv_mulVec]
  -- the kinetic vector `A_κ(x) (Y D(x)⁻¹ h)`
  have hK : ∀ c : N.ComplexIdx,
      (Matrix.mulVec (N.weightedKineticLaplacian κ x)
        (Matrix.mulVec N.complexSpeciesMatrix (Matrix.mulVec (Matrix.diagonal (fun s => 1 / x s)) h))) c
        = ∑ r : N.R, κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
            (∑ s : S, (((N.reaction r).source s : ℝ)) * (h s / x s)) *
            ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)) := by
    intro c
    rw [N.weightedKineticLaplacian_mulVec]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hY]
    rfl
  funext i
  symm
  calc
    (Matrix.mulVec (Matrix.transpose N.complexSpeciesMatrix)
      (Matrix.mulVec (N.weightedKineticLaplacian κ x)
        (Matrix.mulVec N.complexSpeciesMatrix (Matrix.mulVec (Matrix.diagonal (fun s => 1 / x s)) h)))) i
        = ∑ c : N.ComplexIdx, ((c.val i : ℝ)) *
            ((Matrix.mulVec (N.weightedKineticLaplacian κ x)
              (Matrix.mulVec N.complexSpeciesMatrix
                (Matrix.mulVec (Matrix.diagonal (fun s => 1 / x s)) h))) c) := by
          rw [N.complexMatrix_transpose_mulVec]
    _ = ∑ c : N.ComplexIdx, ∑ r : N.R, ((c.val i : ℝ)) *
            (κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
              (∑ s : S, (((N.reaction r).source s : ℝ)) * (h s / x s)) *
              ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0))) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hK c]
          rw [Finset.mul_sum]
    _ = ∑ r : N.R, κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
            (∑ s : S, (((N.reaction r).source s : ℝ)) * (h s / x s)) *
            (∑ c : N.ComplexIdx, ((c.val i : ℝ)) *
              ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          exact sum_mul_factor _ _ _
    _ = ∑ r : N.R, N.massActionRate κ r x *
            (∑ s : S, (((N.reaction r).source s : ℝ)) * (h s / x s)) *
            (N.reactionVector r i) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [sum_mul_sub_ite_complexIdx]
          rw [← N.massActionRate_eq, ← N.reactionVector_apply]
    _ = (N.massActionJacobian κ x).mulVec h i := by
          rw [N.massActionJacobian_mulVec_logform κ hx h]


/-! ## The spectral identity -/

/-- **The spectral factorization of the mass-action Jacobian, in matrix form.**

At a positive concentration `x` the mass-action Jacobian is the product of the transposed
complex matrix, the monomial-weighted kinetic Laplacian, the complex matrix and the inverse
diagonal matrix `D(x)⁻¹`:

```text
J(x) = Yᵀ A_κ(x) Y D(x)⁻¹ .
```

This is the classical Feinberg--Horn--Jackson linearisation of the mass-action field at a
complex-balanced equilibrium. -/
theorem massActionJacobian_eq_factorization (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    N.massActionJacobian κ x =
      Matrix.transpose N.complexSpeciesMatrix * (N.weightedKineticLaplacian κ x *
        (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s))) := by
  classical
  apply Matrix.ext
  intro i j
  have h := congrFun (massActionJacobian_mulVec_eq_factorization N κ hx (coordVec j)) i
  simp only [mulVec_coordVec] at h
  exact h

/-- **The spectral identity.**  The characteristic polynomial of the mass-action Jacobian and
that of the complex-space operator agree up to a power of `X`: the Jacobian is `|S| × |S|` and
the complex-space operator is `|N.ComplexIdx| × |N.ComplexIdx|`, so the two characteristic
polynomials differ only by the corresponding powers of `X`.

This is the classical statement that "the spectrum of the Jacobian is the spectrum of the
kinetic matrix", in the form in which it can be stated without an eigenvalue theory. -/
theorem charpoly_massActionJacobian_mul_comm (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    Polynomial.X ^ Fintype.card N.ComplexIdx * (N.massActionJacobian κ x).charpoly
      = Polynomial.X ^ Fintype.card S * (N.complexSpaceOperator κ x).charpoly := by
  classical
  have h := Matrix.charpoly_mul_comm' (A := Matrix.transpose N.complexSpeciesMatrix)
    (B := N.weightedKineticLaplacian κ x *
      (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s)))
  have hAB : Matrix.transpose N.complexSpeciesMatrix * (N.weightedKineticLaplacian κ x *
      (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s)))
      = N.massActionJacobian κ x := by
    rw [massActionJacobian_eq_factorization N κ hx]
  have hBA : (N.weightedKineticLaplacian κ x *
      (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s))) * Matrix.transpose N.complexSpeciesMatrix
      = N.complexSpaceOperator κ x := by
    rfl
  rw [hAB, hBA] at h
  exact h

/-- **The spectral identity, in the equal-size case.**  When the network has as many complexes
as species the characteristic polynomial of the mass-action Jacobian is *equal* to that of the
complex-space operator. -/
theorem charpoly_massActionJacobian_eq_charpoly_complexSpaceOperator (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hcard : Fintype.card S = Fintype.card N.ComplexIdx) :
    (N.massActionJacobian κ x).charpoly = (N.complexSpaceOperator κ x).charpoly := by
  classical
  have h := charpoly_massActionJacobian_mul_comm N κ hx
  rw [hcard] at h
  exact (Polynomial.isRegular_X_pow (R := ℝ) _).left.eq_iff.mp h

/-- **The spectral identity, in trace form.**  The trace of the mass-action Jacobian is the
trace of the complex-space operator: the two operators have the same spectrum, counted with
multiplicity, in the sense that the sums of the eigenvalues agree. -/
theorem trace_massActionJacobian_eq_trace_complexSpaceOperator (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    Matrix.trace (N.massActionJacobian κ x)
      = Matrix.trace (N.complexSpaceOperator κ x) := by
  classical
  have h := Matrix.trace_mul_comm (A := Matrix.transpose N.complexSpeciesMatrix)
    (B := N.weightedKineticLaplacian κ x *
      (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s)))
  have hAB : Matrix.transpose N.complexSpeciesMatrix * (N.weightedKineticLaplacian κ x *
      (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s)))
      = N.massActionJacobian κ x := by
    rw [massActionJacobian_eq_factorization N κ hx]
  have hBA : (N.weightedKineticLaplacian κ x *
      (N.complexSpeciesMatrix * Matrix.diagonal (fun s => 1 / x s))) * Matrix.transpose N.complexSpeciesMatrix
      = N.complexSpaceOperator κ x := by
    rfl
  rw [hAB, hBA] at h
  exact h

/-- **The spectral identity, in determinant form.**  When the network has as many complexes as
species the determinants of the mass-action Jacobian and of the complex-space operator agree. -/
theorem det_massActionJacobian_eq_det_complexSpaceOperator (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hcard : Fintype.card S = Fintype.card N.ComplexIdx) :
    (N.massActionJacobian κ x).det = (N.complexSpaceOperator κ x).det := by
  classical
  have hchar := charpoly_massActionJacobian_eq_charpoly_complexSpaceOperator N κ hx hcard
  simp only [Matrix.det_eq_sign_charpoly_coeff]
  rw [hcard]
  rw [hchar]


/-! ## The generalized complex balance -/

/-- **The generalized complex balance (Shinohara).**  At a complex-balanced equilibrium the
monomial-weighted kinetic Laplacian annihilates the all-ones vector: the total weighted inflow
and the total weighted outflow of every complex agree.

This is the classical statement that the monomial-weighted adjacency matrix `A_κ` of the
network is *balanced* at `x*`, and it is the structural hypothesis behind the spectral
criterion. -/
theorem weightedKineticLaplacian_mulVec_one_eq_zero_of_complexBalanced (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hcb : N.IsComplexBalanced κ x)
    (c : N.ComplexIdx) :
    (N.weightedKineticLaplacian κ x).mulVec (fun _ => 1) c = 0 := by
  classical
  rw [N.weightedKineticLaplacian_mulVec]
  simp only [mul_one]
  have hsplit : (∑ r : N.R, κ.k r * N.complexMonomialVector x (N.sourceIdx r) *
        ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)))
      = (∑ r : N.R, if N.targetIdx r = c then
          κ.k r * N.complexMonomialVector x (N.sourceIdx r) else 0) -
        (∑ r : N.R, if N.sourceIdx r = c then
          κ.k r * N.complexMonomialVector x (N.sourceIdx r) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h1 : N.targetIdx r = c
    · by_cases h2 : N.sourceIdx r = c
      · simp [h1, h2]
      · simp [h1, h2]
    · by_cases h2 : N.sourceIdx r = c
      · simp [h1, h2]
      · simp [h1, h2]
  rw [hsplit]
  have heqT : ∀ r : N.R, (N.targetIdx r = c) ↔ ((N.reaction r).target = c.val) := by
    intro r
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      simpa [targetIdx] using h'
    · intro h
      apply Subtype.ext
      simp [targetIdx, h]
  have heqS : ∀ r : N.R, (N.sourceIdx r = c) ↔ ((N.reaction r).source = c.val) := by
    intro r
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      simpa [sourceIdx] using h'
    · intro h
      apply Subtype.ext
      simp [sourceIdx, h]
  have hinflow : (∑ r : N.R, if N.targetIdx r = c then
        κ.k r * N.complexMonomialVector x (N.sourceIdx r) else 0)
      = N.inflow κ x c.val := by
    unfold Network.inflow
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : N.targetIdx r = c
    · have h1' : (N.reaction r).target = c.val := (heqT r).mp h1
      simp only [ite_eq_left h1, ite_eq_left h1']
      rw [N.massActionRate_eq]
    · have h1' : (N.reaction r).target ≠ c.val := fun h => h1 ((heqT r).mpr h)
      simp only [ite_eq_right h1, ite_eq_right h1']
  have houtflow : (∑ r : N.R, if N.sourceIdx r = c then
        κ.k r * N.complexMonomialVector x (N.sourceIdx r) else 0)
      = N.outflow κ x c.val := by
    unfold Network.outflow
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : N.sourceIdx r = c
    · have h1' : (N.reaction r).source = c.val := (heqS r).mp h1
      simp only [ite_eq_left h1, ite_eq_left h1']
      rw [N.massActionRate_eq]
    · have h1' : (N.reaction r).source ≠ c.val := fun h => h1 ((heqS r).mpr h)
      simp only [ite_eq_right h1, ite_eq_right h1']
  rw [hinflow, houtflow]
  have hcb' := hcb c.val c.property
  linarith

/-! ## Conservation laws -/

/-- **The mass-action Jacobian annihilates the scaled conservation laws.**  Let `μ` be a vector
of species weights orthogonal to every complex of the network; then the Jacobian at `x`
annihilates `D(x) μ`, the vector with `μ s * x s` in the `s`-th coordinate.

This is the classical statement that the tangent space of the complex-balanced equilibrium
manifold lies in the kernel of the linearisation. -/
theorem massActionJacobian_mulVec_conservationLaw_eq_zero (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) {μ : Concentration S}
    (hμ : ∀ c : N.ComplexIdx, ∑ s : S, μ s * (c.val s : ℝ) = 0) (i : S) :
    (N.massActionJacobian κ x).mulVec (fun s => μ s * x s) i = 0 := by
  classical
  have hD : (Matrix.diagonal (fun s => 1 / x s)).mulVec (fun s => μ s * x s) = μ := by
    funext s
    rw [Matrix.mulVec_diagonal]
    field_simp [(hx s).ne']
  have hY : Matrix.mulVec N.complexSpeciesMatrix μ = 0 := by
    funext c
    rw [N.complexMatrix_mulVec]
    have hc := hμ c
    calc (∑ s : S, ((c.val s : ℝ)) * μ s) = ∑ s : S, μ s * ((c.val s : ℝ)) := by
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ = 0 := hc
  rw [massActionJacobian_mulVec_eq_factorization N κ hx (fun s => μ s * x s)]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hD, hY]
  simp only [Matrix.mulVec_zero]
  rfl

/-! ## The spectral nilpotent criterion -/

/-- A nilpotent matrix has characteristic polynomial `X ^ n`: all its eigenvalues vanish. -/
theorem charpoly_eq_X_pow_of_isNilpotent {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : IsNilpotent M) :
    M.charpoly = Polynomial.X ^ Fintype.card n := by
  obtain ⟨k, hk⟩ := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM
  have hk1 : k ≠ 0 := by
    intro hk0
    subst hk0
    simp at hk
  have h0 : M.charpoly - Polynomial.X ^ Fintype.card n = 0 := (pow_eq_zero_iff hk1).mp hk
  exact sub_eq_zero.mp h0

/-- A matrix whose characteristic polynomial is `X ^ n` is nilpotent: this is the
Cayley--Hamilton theorem. -/
theorem isNilpotent_of_charpoly_eq_X_pow {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.charpoly = Polynomial.X ^ Fintype.card n) : IsNilpotent M := by
  refine ⟨Fintype.card n, ?_⟩
  have h := Matrix.aeval_self_charpoly M
  rw [hM] at h
  rwa [map_pow, Polynomial.aeval_X] at h

set_option maxHeartbeats 800000 in
/-- **The spectral nilpotent criterion.**  At a positive complex-balanced equilibrium the
mass-action Jacobian is nilpotent if and only if the complex-space operator is nilpotent; by
the spectral identity this is the same as saying that *all* the eigenvalues of the
complex-space operator vanish.

This is the spectral form of the classical step "a nilpotent Jacobian makes the kinetic
matrix nilpotent". -/
theorem isNilpotent_massActionJacobian_iff_isNilpotent_complexSpaceOperator (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    IsNilpotent (N.massActionJacobian κ x) ↔ IsNilpotent (N.complexSpaceOperator κ x) := by
  classical
  constructor
  · intro hJ
    have hcharJ : (N.massActionJacobian κ x).charpoly
        = Polynomial.X ^ Fintype.card S :=
      charpoly_eq_X_pow_of_isNilpotent _ hJ
    have h := charpoly_massActionJacobian_mul_comm N κ hx
    rw [hcharJ] at h
    have hkey : Polynomial.X ^ Fintype.card S * (N.complexSpaceOperator κ x).charpoly
        = Polynomial.X ^ Fintype.card S * Polynomial.X ^ Fintype.card N.ComplexIdx := by
      calc Polynomial.X ^ Fintype.card S * (N.complexSpaceOperator κ x).charpoly
          = Polynomial.X ^ Fintype.card N.ComplexIdx * Polynomial.X ^ Fintype.card S := h.symm
        _ = Polynomial.X ^ Fintype.card S * Polynomial.X ^ Fintype.card N.ComplexIdx :=
          mul_comm _ _
    have hcharM : (N.complexSpaceOperator κ x).charpoly
        = Polynomial.X ^ Fintype.card N.ComplexIdx :=
      (Polynomial.isRegular_X_pow (R := ℝ) _).left.eq_iff.mp hkey
    exact isNilpotent_of_charpoly_eq_X_pow _ hcharM
  · intro hM
    have hcharM : (N.complexSpaceOperator κ x).charpoly
        = Polynomial.X ^ Fintype.card N.ComplexIdx :=
      charpoly_eq_X_pow_of_isNilpotent _ hM
    have h := charpoly_massActionJacobian_mul_comm N κ hx
    rw [hcharM] at h
    have hkey : Polynomial.X ^ Fintype.card N.ComplexIdx * (N.massActionJacobian κ x).charpoly
        = Polynomial.X ^ Fintype.card N.ComplexIdx * Polynomial.X ^ Fintype.card S := by
      calc Polynomial.X ^ Fintype.card N.ComplexIdx * (N.massActionJacobian κ x).charpoly
          = Polynomial.X ^ Fintype.card S * Polynomial.X ^ Fintype.card N.ComplexIdx := h
        _ = Polynomial.X ^ Fintype.card N.ComplexIdx * Polynomial.X ^ Fintype.card S :=
          mul_comm _ _
    have hcharJ : (N.massActionJacobian κ x).charpoly
        = Polynomial.X ^ Fintype.card S :=
      (Polynomial.isRegular_X_pow (R := ℝ) _).left.eq_iff.mp hkey
    exact isNilpotent_of_charpoly_eq_X_pow _ hcharJ

set_option maxHeartbeats 800000 in
/-- **The spectral form of the nilpotent-Jacobian criterion.**  At a positive
complex-balanced equilibrium, a nilpotent mass-action Jacobian is equivalent to a complex-space
operator all of whose eigenvalues vanish. -/
theorem charpoly_complexSpaceOperator_eq_X_pow_of_isNilpotent_jacobian (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hnil : IsNilpotent (N.massActionJacobian κ x)) :
    (N.complexSpaceOperator κ x).charpoly
      = Polynomial.X ^ Fintype.card N.ComplexIdx := by
  have hM : IsNilpotent (N.complexSpaceOperator κ x) :=
    (isNilpotent_massActionJacobian_iff_isNilpotent_complexSpaceOperator N κ hx).mp hnil
  exact charpoly_eq_X_pow_of_isNilpotent _ hM

/-! ## The Perron--Frobenius step -/

/-- The powers of an entrywise nonnegative matrix are entrywise nonnegative. -/
theorem pow_nonneg_of_nonneg {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : ∀ i j, 0 ≤ A i j) : ∀ k : ℕ, ∀ i j, 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero =>
    intro i j
    by_cases hij : i = j <;> simp [hij]
  | succ k ih =>
    rw [pow_succ]
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

/-- The powers of an entrywise strictly positive matrix are entrywise strictly positive. -/
theorem pow_pos_of_pos {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hm : ∀ i j, 0 < A i j) : ∀ k : ℕ, k ≥ 1 → ∀ i j, 0 < (A ^ k) i j := by
  have hmain : ∀ k : ℕ, (∀ i j, 0 < (A ^ k) i j) ∨ k = 0 := by
    intro k
    induction k with
    | zero => exact Or.inr rfl
    | succ k ih =>
      rcases ih with ih | hk
      · left
        rw [pow_succ]
        intro i j
        rw [Matrix.mul_apply]
        refine Finset.sum_pos' (fun l _ => mul_nonneg (ih i l).le (hm l j).le)
          ⟨i, Finset.mem_univ i, ?_⟩
        exact mul_pos (ih i i) (hm i j)
      · left
        subst hk
        simpa using hm
  intro k hk
  rcases hmain k with h | h
  · exact h
  · omega

set_option linter.unusedVariables false in
/-- **The Perron--Frobenius step.**  An entrywise nonnegative matrix that has a strictly
positive power is not nilpotent.

Indeed, if `P` were nilpotent, say `P^k = 0`, then also `P^(k+1) = 0`; but
`P^(m (k+1)) = (P^m)^(k+1)` is entrywise positive, because a nonnegative matrix with a
strictly positive power has strictly positive powers as well.

This is the classical ingredient that turns the nilpotency of the kinetic data into the
triviality of the network: a nonnegative matrix whose support digraph is strongly connected
(so that some power is strictly positive) cannot be nilpotent unless it vanishes. -/
theorem not_isNilpotent_of_nonneg_of_pos_mulVec {n : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hm : ∃ m : ℕ, m ≥ 1 ∧ ∀ i j, 0 < (P ^ m) i j) : ¬ IsNilpotent P := by
  classical
  obtain ⟨m, hm1, hmpos⟩ := hm
  obtain ⟨i⟩ := ‹Nonempty n›
  rintro ⟨k, hk⟩
  have hk1 : P ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  have hpos : ∀ j l, 0 < ((P ^ m) ^ (k + 1)) j l :=
    pow_pos_of_pos (P ^ m) hmpos (k + 1) (by omega)
  have hz : P ^ (m * (k + 1)) = 0 := by
    calc P ^ (m * (k + 1)) = P ^ ((k + 1) * m) := by rw [Nat.mul_comm]
      _ = (P ^ (k + 1)) ^ m := by rw [pow_mul]
      _ = 0 := by rw [hk1, zero_pow (by omega)]
  have heq : (P ^ m) ^ (k + 1) = P ^ (m * (k + 1)) := by
    rw [pow_mul]
  rw [heq, hz] at hpos
  exact absurd (hpos i i) (by simp)

/-- **The Perron--Frobenius criterion for the weighted adjacency matrix.**  At a positive
concentration the monomial-weighted adjacency matrix is entrywise nonnegative; if it has a
strictly positive power, it is not nilpotent, and hence it is not the zero matrix. -/
theorem not_isNilpotent_weightedAdjacencyMatrix_of_pos_mulVec (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hc : Nonempty N.ComplexIdx)
    (hm : ∃ m : ℕ, m ≥ 1 ∧ ∀ c d : N.ComplexIdx, 0 < (N.weightedAdjacencyMatrix κ x ^ m) c d) :
    ¬ IsNilpotent (N.weightedAdjacencyMatrix κ x) := by
  classical
  exact not_isNilpotent_of_nonneg_of_pos_mulVec (N.weightedAdjacencyMatrix κ x)
    (N.weightedAdjacencyMatrix_nonneg κ hx) hm


/-! ## A concrete instance

The network `A ⇄ B` with the rate constants `1` (for `A → B`) and `2` (for `B → A`) is
complex balanced at `x* = (2, 1)`: the inflow and the outflow of `A` are both `2`, and so are
those of `B`.  At that equilibrium the mass-action Jacobian is `[[-1, 2], [1, -2]]`, whose
characteristic polynomial is `X^2 + 3X`; the spectral identity says that the complex-space
operator has the same characteristic polynomial. -/

end Network

namespace Examples.JacobianSpectrum

open CRNT

/-- Two species, `A` and `B`. -/
abbrev Species := Fin 2

/-- Two reaction channels. -/
abbrev Rxn := Fin 2

/-- The complex `A`. -/
def cA : Complex Species := fun s => if s = 0 then 1 else 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => if s = 1 then 1 else 0

/-- The reaction channel `A → B`. -/
def r0 : Rxn := ⟨0, by norm_num⟩

/-- The reaction channel `B → A`. -/
def r1 : Rxn := ⟨1, by norm_num⟩

/-- The reaction map: the first channel is `A → B`, the second one is `B → A`. -/
def rxn : Rxn → Reaction Species := fun r =>
  if r = r0 then { source := cA, target := cB } else { source := cB, target := cA }

/-- The network `A ⇄ B`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The rate constant of a reaction channel. -/
def kfun : Rxn → ℝ := fun r => if r = r0 then 1 else 2

/-- The rate constants: `1` for `A → B` and `2` for `B → A`. -/
def rates : Network.RateConstants N where
  k := fun r => kfun (r : Rxn)
  positive := by
    intro r
    have : 0 < kfun (r : Rxn) := by
      fin_cases r <;> simp [kfun, r0]
    exact this

/-- The complex-balanced equilibrium `x* = (2, 1)`. -/
def xstar : Concentration Species := fun s => if s = 0 then 2 else 1

/-- The equilibrium `x*` is positive. -/
theorem xstar_positive : xstar.Positive := by
  intro s
  fin_cases s <;> simp [xstar]

/-- The mass-action Jacobian at the complex-balanced equilibrium. -/
theorem massActionJacobian_eq :
    N.massActionJacobian rates xstar = !![-1, 2; 1, -2] := by
  funext i j
  simp only [Network.massActionJacobian]
  have hsum : (∑ r : N.R, rates.k r * massActionMonomialGrad (N.reaction r).source xstar j
      * N.reactionVector r i)
      = ∑ r : Rxn, rates.k r * massActionMonomialGrad (N.reaction r).source xstar j
        * N.reactionVector r i := rfl
  rw [hsum]
  fin_cases i <;> fin_cases j <;>
    simp [Network.reactionVector, massActionMonomialGrad,
      N, rxn, r0, cA, cB, rates, kfun, xstar]

/-- The characteristic polynomial of the mass-action Jacobian at the complex-balanced
equilibrium: `X^2 + 3X`. -/
theorem charpoly_massActionJacobian :
    (N.massActionJacobian rates xstar).charpoly = Polynomial.X ^ 2 + 3 * Polynomial.X := by
  rw [massActionJacobian_eq]
  rw [Matrix.charpoly_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two]
  norm_num
  rfl

/-- **The spectral identity, checked numerically.**  At the complex-balanced equilibrium of
the network `A ⇄ B` the characteristic polynomial of the mass-action Jacobian is `X^2 + 3X`,
and the spectral identity says that the complex-space operator has the same characteristic
polynomial, up to the powers of `X` that account for the different sizes of the two matrices. -/
theorem charpoly_massActionJacobian_mul_comm :
    Polynomial.X ^ Fintype.card N.ComplexIdx * (N.massActionJacobian rates xstar).charpoly
      = Polynomial.X ^ Fintype.card Species * (N.complexSpaceOperator rates xstar).charpoly := by
  exact N.charpoly_massActionJacobian_mul_comm rates xstar_positive

/-- **The trace form of the spectral identity, checked numerically.** -/
theorem trace_massActionJacobian_eq_trace_complexSpaceOperator :
    Matrix.trace (N.massActionJacobian rates xstar)
      = Matrix.trace (N.complexSpaceOperator rates xstar) := by
  exact N.trace_massActionJacobian_eq_trace_complexSpaceOperator rates xstar_positive

end Examples.JacobianSpectrum

/-! ### The nilpotent case: the self-loop network `A → A`

The self-loop network of `CRNT.Examples.NilpotentJacobian` is the case in which the
nilpotent-Jacobian hypothesis of the classical criterion holds: its mass-action Jacobian is
the zero matrix at every concentration, so its characteristic polynomial is `X` — all the
eigenvalues vanish — and the spectral identity says that the complex-space operator has the
same characteristic polynomial. -/

namespace Examples.NilpotentJacobian

/-- **The spectral identity at the complex-balanced equilibrium of the self-loop network.**
The mass-action Jacobian is the zero matrix, so its characteristic polynomial is `X`: all its
eigenvalues vanish, and the spectral identity says that the complex-space operator has the
same characteristic polynomial. -/
theorem charpoly_massActionJacobian (k : ℝ) (hk : 0 < k) :
    (N.massActionJacobian (rates k hk) (fun _ => 1)).charpoly = Polynomial.X := by
  rw [massActionJacobian_eq_zero]
  simp [Matrix.charpoly_zero]

/-- **The spectral nilpotent criterion at work.**  The complex-space operator of the self-loop
network is nilpotent at the complex-balanced equilibrium: the spectral identity transfers the
nilpotency of the mass-action Jacobian to the complex-space operator, whose eigenvalues all
vanish. -/
theorem isNilpotent_complexSpaceOperator (k : ℝ) (hk : 0 < k) :
    IsNilpotent (N.complexSpaceOperator (rates k hk) (fun _ => 1)) := by
  have hnil : IsNilpotent (N.massActionJacobian (rates k hk) (fun _ => 1)) := by
    rw [massActionJacobian_eq_zero]
    exact ⟨1, by simp⟩
  exact (N.isNilpotent_massActionJacobian_iff_isNilpotent_complexSpaceOperator (rates k hk)
    (by intro s; simp)).mp hnil

end Examples.NilpotentJacobian

end CRNT
