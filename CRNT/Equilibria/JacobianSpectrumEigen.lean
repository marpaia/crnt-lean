import CRNT.Equilibria.JacobianSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# The eigenvalue theory of the nilpotent-Jacobian criterion, and the primitive-matrix form

This module completes field-map leaf **S20** (the nilpotent-Jacobian criterion for complex
balance) in the two directions that were still open, and it records precisely what remains
out of reach.

## The criterion

For a mass-action network `N` with rate constants `κ` the mass-action field factorises
(`CRNT.Dynamics.MassActionAlgebra`) as `ẋ = Y (A_κ Ψ x)`, with `Y` the complex matrix, `A_κ` the
kinetic matrix of the reaction graph and `Ψ` the monomial map.  The **nilpotent-Jacobian
criterion** of Horn--Jackson (1972, 1974; see also G. Craciun, *Chemical reaction network
theory*, AMS 2020, Chapter 4) says that at a *complex-balanced* equilibrium `x*` the
mass-action Jacobian `J(x*)` can be nilpotent only for a *dynamically trivial* network, i.e. a
network whose reactions are all self-loops.  The repository proves this in the entropy metric
(`CRNT.Equilibria.NilpotentJacobian`): the Horn--Jackson sum-of-squares identity makes the
entropy-Hessian pairing of `J(x*)` a nonpositive sum of squares, and a nilpotent matrix with a
nonpositive quadratic form vanishes.  The spectral counterpart is
`CRNT.Equilibria.JacobianSpectrum`.

## The Perron--Frobenius theory of nonnegative matrices

The classical ingredient of the criterion is the Perron--Frobenius theory of **nonnegative**
matrices: a nonnegative matrix that has a strictly positive power is not nilpotent, and a
nonnegative matrix whose support digraph is strongly connected (Mathlib: `Matrix.IsIrreducible`)
is not nilpotent either.  The repository used the ad-hoc hypothesis "there is a positive entry
in some power" (`CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_pos_mulVec`); this
module replaces it by Mathlib's **named** notions

* `Matrix.IsPrimitive` — entrywise nonnegative with a strictly positive power, and
* `Matrix.IsIrreducible` — entrywise nonnegative with strongly connected support digraph,

in the theorems `CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive` and
`CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isIrreducible`.

**What is still out of reach.**  Mathlib has no Perron--Frobenius theorem: there is no
`spectralRadius_eq_max_realOf_eigenvalues`, no Perron root, and no `Matrix.eigenvalues`.
Consequently the *spectral radius* form of the classical step — "a primitive nonnegative matrix
has a positive eigenvalue, namely its spectral radius" — cannot be stated here, and neither can
the classical conclusion "the kinetic matrix of a weakly reversible network is irreducible, hence
its spectral radius is positive, hence the Jacobian is not nilpotent".  What *is* proved below
is the weaker but classical statement "a primitive (respectively irreducible) nonnegative matrix
is not nilpotent", together with the consequence for the criterion
(`CRNT.Network.not_isNilpotentJacobian_of_isPrimitive`).

## The eigenvalue theory

Mathlib has no `Matrix.eigenvalues`; eigenvalues are named only through
`Module.End.HasEigenvalue μ` (an `μ` such that `f x = μ • x` for some `x ≠ 0`) and through the
*spectrum* of an endomorphism.  The bridge between the two is
`Module.End.hasEigenvalue_iff_isRoot_charpoly` : an `μ` is an eigenvalue of `f` if and only if
`μ` is a root of the characteristic polynomial of `f`.  This module uses it to name the
eigenvalues of the mass-action Jacobian and to prove the *explicit eigenvalue theory* of the
criterion:

```text
J(x*) is nilpotent   ⟺   every (complex) eigenvalue of J(x*) is 0.
```

(`CRNT.Network.isNilpotent_massActionJacobian_iff_eigenvalues_zero`, and its companion
`CRNT.Network.isNilpotent_complexSpaceOperator_iff_eigenvalues_zero` for the complex-space
operator of `CRNT.Equilibria.JacobianSpectrum`.)

The eigenvalues are those of the **complexification** of the real Jacobian: the mass-action
Jacobian is a real `|S| × |S|` matrix, while the eigenvalues are complex.  The embedding of a real
matrix into a complex one is `CRNT.Network.complexifyMatrix`, and nilpotence is equivalent for a
matrix and its complexification.

## A remark on the naive form of the statement

The often-quoted slogan "the eigenvalues of the Jacobian at a complex-balanced equilibrium are
the negatives of the eigenvalues of the bare weighted adjacency matrix" is **false**, and the
repository refutes it by proof (`CRNT.Network.massActionJacobian_eq_factorization` and the
reversible-pair example `CRNT.Examples.JacobianSpectrum`: for `A ⇄ B` with rates `1` and `2` at
`x* = (2, 1)` the Jacobian has characteristic polynomial `X^2 + 3X` while the bare weighted
adjacency matrix has `X^2 - 4`; the two matrices do not even have the same size).  What is
correct is the **factorization-based** form, proved in `CRNT.Equilibria.JacobianSpectrum`:

```text
J(x) = Yᵀ A_κ(x) Y D(x)⁻¹ ,   X^{|complexes|} · charpoly J = X^{|species|} · charpoly M ,
```

with `M` the complex-space operator.  Only this form is used here: the eigenvalue theory of the
criterion is stated for the Jacobian itself, and no identification of the eigenvalues of the
Jacobian with those of the bare weighted adjacency matrix is made.

## A remark on the nilpotent-Jacobian criterion and primitivity

Primitivity of the weighted adjacency matrix does **not** by itself rule out a nilpotent
Jacobian: the self-loop network `A → A` (`CRNT.Examples.NilpotentJacobian`) has the positive
`1 × 1` weighted adjacency matrix `[k]`, which is primitive, while its mass-action Jacobian is
the zero matrix.  The classical conclusion therefore needs the network to be *non-trivial*; the
theorem `CRNT.Network.not_isNilpotentJacobian_of_isPrimitive` below states the version in which
the primitivity hypothesis does genuine work: at a positive complex-balanced equilibrium of a
network with at least two complexes, a primitive weighted adjacency matrix rules out a nilpotent
Jacobian.

Depends on: `CRNT.Equilibria.JacobianSpectrum`, Mathlib `LinearAlgebra.Eigenspace.Charpoly`,
`LinearAlgebra.Matrix.Irreducible.Defs`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The complexification of a real matrix -/

/-- The **complexification** of a real matrix: the same matrix with complex entries.  It is the
embedding that turns the real mass-action Jacobian into an operator on a complex vector space,
where eigenvalues live. -/
def complexifyMatrix {n : Type} (M : Matrix n n ℝ) : Matrix n n ℂ :=
  M.map (fun r => (r : ℂ))

/-- Entrywise, the complexification of a real matrix is the complex matrix with the same
entries. -/
theorem complexifyMatrix_apply {n : Type} (M : Matrix n n ℝ) (i j : n) :
    complexifyMatrix M i j = (M i j : ℂ) := rfl

/-- The complexification is a ring homomorphism on matrices. -/
theorem complexifyMatrix_mul {n : Type} [Fintype n] [DecidableEq n] (M N : Matrix n n ℝ) :
    complexifyMatrix (M * N) = complexifyMatrix M * complexifyMatrix N := by
  rw [complexifyMatrix, complexifyMatrix, complexifyMatrix]
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-- The complexification of the zero matrix is the zero matrix. -/
theorem complexifyMatrix_zero {n : Type} [Fintype n] [DecidableEq n] :
    complexifyMatrix (0 : Matrix n n ℝ) = 0 := by
  ext i j
  simp [complexifyMatrix]

/-- The complexification commutes with powers. -/
theorem complexifyMatrix_pow {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (k : ℕ) :
    complexifyMatrix (M ^ k) = complexifyMatrix M ^ k := by
  induction k with
  | zero => simp [complexifyMatrix]
  | succ k ih => rw [pow_succ, complexifyMatrix_mul, ih, pow_succ]

/-- **A real matrix is nilpotent if and only if its complexification is.**  Nilpotence is a
statement about powers, and the powers of a real matrix and of its complexification agree
entrywise. -/
theorem isNilpotent_complexifyMatrix_iff {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : IsNilpotent M ↔ IsNilpotent (complexifyMatrix M) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← complexifyMatrix_pow, hk, complexifyMatrix_zero]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hmap : complexifyMatrix (M ^ k) = 0 := by
      rw [complexifyMatrix_pow]
      exact hk
    apply Matrix.ext
    intro i j
    have h := congrFun (congrFun hmap i) j
    simp only [complexifyMatrix_apply, Matrix.zero_apply] at h
    exact Complex.ofReal_eq_zero.mp h

/-! ## The eigenvalue theory of nilpotent matrices -/

section ComplexSpectrum

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The linear map associated with the zero matrix is the zero linear map. -/
theorem toLin'_zero {R : Type} [CommSemiring R] {n : Type} [Fintype n] [DecidableEq n] :
    (0 : Matrix n n R).toLin' = 0 := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.zero_mulVec]
  rfl

/-- **Cayley--Hamilton.**  A matrix whose characteristic polynomial is `X ^ n` is nilpotent.  This
is the same statement as `CRNT.Network.isNilpotent_of_charpoly_eq_X_pow`, but over an arbitrary
commutative ring. -/
theorem isNilpotent_of_charpoly_eq_X_pow_complex {R : Type} [CommRing R]
    (M : Matrix n n R) (hM : M.charpoly = Polynomial.X ^ Fintype.card n) : IsNilpotent M := by
  refine ⟨Fintype.card n, ?_⟩
  have h := Matrix.aeval_self_charpoly M
  rw [hM] at h
  rwa [map_pow, Polynomial.aeval_X] at h

/-- **The explicit eigenvalue theory: over the complex numbers, a matrix is nilpotent if and
only if all of its eigenvalues vanish.**

An eigenvalue of `M` is a complex number `μ` for which `M v = μ • v` for some `v ≠ 0`
(`Module.End.HasEigenvalue`).  The proof uses the bridge between eigenvalues and roots of the
characteristic polynomial (`Module.End.hasEigenvalue_iff_isRoot_charpoly`), the fact that the
characteristic polynomial of a complex matrix splits (`IsAlgClosed.splits`), and the Cayley--
Hamilton theorem. -/
theorem isNilpotent_iff_eigenvalues_zero (M : Matrix n n ℂ) :
    IsNilpotent M ↔
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → μ = 0 := by
  constructor
  · intro hnil μ hμ
    obtain ⟨k, hk⟩ := hnil
    -- the linear map of `M` is nilpotent
    have hlin : (Matrix.toLin' M : Module.End ℂ (n → ℂ)) ^ k = 0 := by
      rw [← Matrix.toLin'_pow]
      have hz : (M ^ k).toLin' = 0 := by
        rw [hk]
        exact toLin'_zero
      rw [hz]
    -- a nilpotent endomorphism has nilpotent eigenvalues, and a nilpotent complex number is 0
    have hμnil : IsNilpotent μ := hμ.isNilpotent_of_isNilpotent ⟨k, hlin⟩
    exact hμnil.eq_zero
  · intro h
    -- the characteristic polynomial of `M` is `X ^ n`
    have hchar : M.charpoly = Polynomial.X ^ Fintype.card n := by
      have hmono : M.charpoly.Monic := M.charpoly_monic
      have hsplit : M.charpoly.Splits := IsAlgClosed.splits M.charpoly
      have hprod : M.charpoly
          = (M.charpoly.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod :=
        hsplit.eq_prod_roots_of_monic hmono
      have hne : M.charpoly ≠ 0 := hmono.ne_zero
      -- every root of the characteristic polynomial is an eigenvalue, hence is 0
      have hroot : ∀ r ∈ M.charpoly.roots, r = 0 := by
        intro r hr
        have hroot' : M.charpoly.IsRoot r := (Polynomial.mem_roots hne).mp hr
        rw [← Matrix.charpoly_toLin'] at hroot'
        have hμ : Module.End.HasEigenvalue (Matrix.toLin' M) r :=
          (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot'
        exact h r hμ
      have hmap : M.charpoly.roots.map (fun x => Polynomial.X - Polynomial.C x)
          = M.charpoly.roots.map (fun _ => Polynomial.X) := by
        apply Multiset.map_congr rfl
        intro x hx
        have hx0 := hroot x hx
        simp [hx0]
      calc M.charpoly = (M.charpoly.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod := hprod
        _ = (M.charpoly.roots.map (fun _ => Polynomial.X)).prod := by rw [hmap]
        _ = Polynomial.X ^ M.charpoly.roots.card := by
          simp [Multiset.map_const', Multiset.prod_replicate]
        _ = Polynomial.X ^ Fintype.card n := by
          congr 1
          rw [← hsplit.natDegree_eq_card_roots, M.charpoly_natDegree_eq_dim]
    exact isNilpotent_of_charpoly_eq_X_pow_complex M hchar

end ComplexSpectrum

/-! ## The eigenvalue form of the nilpotent-Jacobian criterion -/

set_option linter.unusedVariables false in
/-- **The explicit eigenvalue theory of the nilpotent-Jacobian criterion.**

The mass-action Jacobian at a positive concentration `x` is nilpotent exactly when every one of
its (complex) eigenvalues is zero.  This is the *explicit eigenvalue theory* that the field map
asks for: until now the characteristic polynomial was the only surrogate for the eigenvalues.

The eigenvalues are those of the complexification of the real Jacobian, the eigenvalues being
complex numbers (`Module.End.HasEigenvalue`) while the Jacobian is a real matrix. -/
theorem isNilpotent_massActionJacobian_iff_eigenvalues_zero
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    N.IsNilpotentJacobian κ x ↔
      ∀ μ : ℂ,
        Module.End.HasEigenvalue (Matrix.toLin' (complexifyMatrix (N.massActionJacobian κ x))) μ →
          μ = 0 := by
  rw [Network.IsNilpotentJacobian]
  constructor
  · intro hnil μ hμ
    have hnilC : IsNilpotent (complexifyMatrix (N.massActionJacobian κ x)) :=
      (isNilpotent_complexifyMatrix_iff _).mp hnil
    exact (isNilpotent_iff_eigenvalues_zero (complexifyMatrix (N.massActionJacobian κ x))).mp
      hnilC μ hμ
  · intro h
    have hnilC : IsNilpotent (complexifyMatrix (N.massActionJacobian κ x)) :=
      (isNilpotent_iff_eigenvalues_zero (complexifyMatrix (N.massActionJacobian κ x))).mpr h
    exact (isNilpotent_complexifyMatrix_iff _).mpr hnilC

set_option linter.unusedVariables false in
/-- **The eigenvalue form of the spectral nilpotent criterion.**  At a positive complex-balanced
equilibrium the mass-action Jacobian is nilpotent if and only if the complex-space operator is
nilpotent, i.e. if and only if all the eigenvalues of the complex-space operator vanish. -/
theorem isNilpotent_complexSpaceOperator_iff_eigenvalues_zero
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    IsNilpotent (N.complexSpaceOperator κ x) ↔
      ∀ μ : ℂ,
        Module.End.HasEigenvalue (Matrix.toLin' (complexifyMatrix (N.complexSpaceOperator κ x))) μ →
          μ = 0 := by
  constructor
  · intro hnil μ hμ
    have hnilC : IsNilpotent (complexifyMatrix (N.complexSpaceOperator κ x)) :=
      (isNilpotent_complexifyMatrix_iff _).mp hnil
    exact (isNilpotent_iff_eigenvalues_zero (complexifyMatrix (N.complexSpaceOperator κ x))).mp
      hnilC μ hμ
  · intro h
    have hnilC : IsNilpotent (complexifyMatrix (N.complexSpaceOperator κ x)) :=
      (isNilpotent_iff_eigenvalues_zero (complexifyMatrix (N.complexSpaceOperator κ x))).mpr h
    exact (isNilpotent_complexifyMatrix_iff _).mpr hnilC

/-! ## The Perron--Frobenius step in the classical forms -/

/-- **The Perron--Frobenius step in its classical "primitive matrix" form.**  A primitive
nonnegative matrix — entrywise nonnegative with a strictly positive power — is not nilpotent.

This replaces the repository's ad-hoc hypothesis "there is a positive entry in some power" by
Mathlib's named notion of primitivity.

The hypothesis `Nonempty N.ComplexIdx` is needed: for a network with no reaction at all the
weighted adjacency matrix is the empty matrix, which is (vacuously) primitive and nilpotent at
the same time.  The same hypothesis occurs in the repository's earlier version of the step,
`CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_pos_mulVec`. -/
theorem not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hc : Nonempty N.ComplexIdx)
    (hprim : Matrix.IsPrimitive (N.weightedAdjacencyMatrix κ x)) :
    ¬ IsNilpotent (N.weightedAdjacencyMatrix κ x) := by
  classical
  obtain ⟨k, hk, hpos⟩ := hprim.exists_pos_pow
  exact not_isNilpotent_of_nonneg_of_pos_mulVec (N.weightedAdjacencyMatrix κ x)
    (N.weightedAdjacencyMatrix_nonneg κ hx) ⟨k, by omega, hpos⟩

/-- **The Perron--Frobenius step, in the general form.**  A nonnegative matrix whose support
digraph is strongly connected — Mathlib: `Matrix.IsIrreducible` — is not nilpotent.

Indeed, if `A^k = 0` then `A^m = 0` for every `m ≥ k`; but irreducibility gives, for every `i`,
a power `A^m` with a positive `i`-th diagonal entry, and a nonnegative matrix with a positive
diagonal entry has positive diagonal entries in all its powers, which contradicts
`A^m = 0` for `m` large enough. -/
theorem not_isNilpotent_of_nonneg_of_exists_pow_pos {n : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hm : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j) : ¬ IsNilpotent A := by
  classical
  rintro ⟨k, hk⟩
  have hzero : ∀ m : ℕ, k ≤ m → A ^ m = 0 := by
    intro m hm
    have hkm : m = k + (m - k) := by omega
    rw [hkm, pow_add, hk, zero_mul]
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  obtain ⟨m, hm0, hmpos⟩ := hm i i
  have hA' : ∀ j k, 0 ≤ (A ^ m) j k := pow_nonneg_of_nonneg A hA m
  -- a nonnegative matrix with a positive diagonal entry has positive diagonal entries in all
  -- its powers
  have hprop : ∀ t : ℕ, 1 ≤ t → 0 < ((A ^ m) ^ t) i i := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      intro ht
      by_cases hzero' : t = 0
      · subst hzero'
        simpa [pow_one] using hmpos
      · have ih' := ih (by omega)
        have hA'' : ∀ j k, 0 ≤ ((A ^ m) ^ t) j k := pow_nonneg_of_nonneg (A ^ m) hA' t
        rw [pow_succ, Matrix.mul_apply]
        refine Finset.sum_pos' (fun l _ => mul_nonneg (hA'' i l) (hA' l i))
          ⟨i, Finset.mem_univ i, ?_⟩
        exact mul_pos ih' hmpos
  have hkm : k ≤ m * (k + 1) := by
    have h1 : 1 * (k + 1) ≤ m * (k + 1) := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (k + 1) (show 1 ≤ m from hm0)
    have h2 : k ≤ 1 * (k + 1) := by simp
    exact h2.trans h1
  have hpos : 0 < ((A ^ m) ^ (k + 1)) i i := hprop (k + 1) (by omega)
  rw [← pow_mul] at hpos
  have hz : A ^ (m * (k + 1)) = 0 := hzero _ hkm
  rw [hz] at hpos
  simp at hpos

/-- **The Perron--Frobenius step in the "irreducible" form.**  A nonnegative matrix whose support
digraph is strongly connected (Mathlib: `Matrix.IsIrreducible`) is not nilpotent.

As above, the hypothesis `Nonempty N.ComplexIdx` is needed to exclude the empty matrix. -/
theorem not_isNilpotent_weightedAdjacencyMatrix_of_isIrreducible
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hc : Nonempty N.ComplexIdx)
    (hirr : Matrix.IsIrreducible (N.weightedAdjacencyMatrix κ x)) :
    ¬ IsNilpotent (N.weightedAdjacencyMatrix κ x) := by
  classical
  have hnonneg : ∀ i j, 0 ≤ (N.weightedAdjacencyMatrix κ x) i j :=
    N.weightedAdjacencyMatrix_nonneg κ hx
  have hm : ∀ i j, ∃ k > 0, 0 < (N.weightedAdjacencyMatrix κ x ^ k) i j :=
    (Matrix.isIrreducible_iff_exists_pow_pos hnonneg).mp hirr
  exact not_isNilpotent_of_nonneg_of_exists_pow_pos (N.weightedAdjacencyMatrix κ x) hnonneg hm

/-! ## The Perron--Frobenius consequence for the nilpotent-Jacobian criterion -/

/-- **The powers of a diagonal matrix are diagonal.** -/
theorem pow_apply_eq_zero_of_ne {n : Type} [Fintype n] [DecidableEq n] (D : Matrix n n ℝ)
    (hD : ∀ i j, i ≠ j → D i j = 0) (k : ℕ) (i j : n) (hij : i ≠ j) : (D ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero => simp [hij]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hli : l = i
    · have hlj : l ≠ j := hli ▸ hij
      rw [hD l j hlj]
      ring
    · rw [ih i l (Ne.symm hli)]
      ring

set_option linter.unusedVariables false in
/-- **The classical Perron--Frobenius consequence for the nilpotent-Jacobian criterion.**

At a positive complex-balanced equilibrium the nilpotent-Jacobian criterion forces every
reaction of the network to be stoichiometrically null, i.e. to be a self-loop; the weighted
adjacency matrix of the network is then diagonal.  If in addition the weighted adjacency matrix
is *primitive* and the network has at least two complexes, this is impossible: a primitive matrix
has a strictly positive power, hence a positive off-diagonal entry, whereas a diagonal matrix
has none.  So the nilpotent-Jacobian criterion cannot apply.

This is the classical Horn--Jackson conclusion in the repository's own terms: the Perron--
Frobenius input is the primitivity (or the weaker hypothesis of irreducibility) of the weighted
adjacency matrix, and the conclusion is that the Jacobian of a non-trivial network is not
nilpotent.

The hypothesis `2 ≤ Fintype.card N.ComplexIdx` (the network is not a single self-loop) is
*necessary*: without it the statement is false, since the self-loop network `A → A` has a
primitive weighted adjacency matrix and a nilpotent mass-action Jacobian
(`CRNT.Examples.NilpotentJacobian.isPrimitive_weightedAdjacencyMatrix_of_isNilpotentJacobian`). -/
theorem not_isNilpotentJacobian_of_isPrimitive
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hcb : N.IsComplexBalanced κ x)
    (hprim : Matrix.IsPrimitive (N.weightedAdjacencyMatrix κ x))
    (hcard : 2 ≤ Fintype.card N.ComplexIdx) :
    ¬ N.IsNilpotentJacobian κ x := by
  classical
  intro hnil
  -- the criterion forces every reaction to be a self-loop
  have hnull : ∀ r : N.R, N.reactionVector r = 0 :=
    N.reactionVector_eq_zero_of_nilpotent_jacobian_of_all κ hx hcb hnil
  have hself : ∀ r : N.R, (N.reaction r).source = (N.reaction r).target := by
    intro r
    funext s
    have h := congrFun (hnull r) s
    simp only [Network.reactionVector_apply] at h
    have h' : (N.reaction r).source s = (N.reaction r).target s := by
      have h'' : ((N.reaction r).target s : ℝ) = (N.reaction r).source s := sub_eq_zero.mp h
      exact_mod_cast h''.symm
    exact h'
  -- hence the weighted adjacency matrix is diagonal
  have hdiag : ∀ c d : N.ComplexIdx, c ≠ d → (N.weightedAdjacencyMatrix κ x) c d = 0 := by
    intro c d hcd
    unfold Network.weightedAdjacencyMatrix
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hsrc : N.sourceIdx r = d
    · have htg : N.targetIdx r = d := by
        have hsd : d = N.sourceIdx r := hsrc.symm
        rw [hsd]
        apply Subtype.ext
        change (N.reaction r).target = (N.reaction r).source
        exact (hself r).symm
      have hne : ¬ (N.targetIdx r = c) := fun h => hcd (h ▸ htg)
      simp only [ite_eq_left hsrc, ite_eq_right hne]
    · simp only [ite_eq_right hsrc]
  -- but a primitive matrix has a strictly positive power, hence a positive off-diagonal entry
  obtain ⟨k, hk, hpos⟩ := hprim.exists_pos_pow
  have hne : Nontrivial N.ComplexIdx := by
    by_contra hc
    have h1 : ∀ a b : N.ComplexIdx, a = b := by
      intro a b
      by_contra hne
      exact hc ⟨a, b, hne⟩
    have h2 : Fintype.card N.ComplexIdx ≤ 1 := (Fintype.card_le_one_iff).mpr h1
    omega
  obtain ⟨c, d, hcd⟩ := exists_pair_ne N.ComplexIdx
  have h1 : (N.weightedAdjacencyMatrix κ x ^ k) c d = 0 :=
    pow_apply_eq_zero_of_ne (N.weightedAdjacencyMatrix κ x) hdiag k c d hcd
  exact absurd (hpos c d) (by rw [h1]; exact lt_irrefl _)

set_option linter.unusedVariables false in
/-- **The Perron--Frobenius consequence for the nilpotent-Jacobian criterion, in the
irreducible form.**  Irreducibility of the weighted adjacency matrix plays the same role as
primitivity: irreducibility gives, for every pair of complexes, a power with a positive
off-diagonal entry, which a diagonal matrix cannot have. -/
theorem not_isNilpotentJacobian_of_isIrreducible
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hcb : N.IsComplexBalanced κ x)
    (hirr : Matrix.IsIrreducible (N.weightedAdjacencyMatrix κ x))
    (hcard : 2 ≤ Fintype.card N.ComplexIdx) :
    ¬ N.IsNilpotentJacobian κ x := by
  classical
  intro hnil
  -- the criterion forces every reaction to be a self-loop, hence the adjacency matrix is
  -- diagonal
  have hnull : ∀ r : N.R, N.reactionVector r = 0 :=
    N.reactionVector_eq_zero_of_nilpotent_jacobian_of_all κ hx hcb hnil
  have hself : ∀ r : N.R, (N.reaction r).source = (N.reaction r).target := by
    intro r
    funext s
    have h := congrFun (hnull r) s
    simp only [Network.reactionVector_apply] at h
    have h' : (N.reaction r).source s = (N.reaction r).target s := by
      have h'' : ((N.reaction r).target s : ℝ) = (N.reaction r).source s := sub_eq_zero.mp h
      exact_mod_cast h''.symm
    exact h'
  have hdiag : ∀ c d : N.ComplexIdx, c ≠ d → (N.weightedAdjacencyMatrix κ x) c d = 0 := by
    intro c d hcd
    unfold Network.weightedAdjacencyMatrix
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hsrc : N.sourceIdx r = d
    · have htg : N.targetIdx r = d := by
        have hsd : d = N.sourceIdx r := hsrc.symm
        rw [hsd]
        apply Subtype.ext
        change (N.reaction r).target = (N.reaction r).source
        exact (hself r).symm
      have hne : ¬ (N.targetIdx r = c) := fun h => hcd (h ▸ htg)
      simp only [ite_eq_left hsrc, ite_eq_right hne]
    · simp only [ite_eq_right hsrc]
  -- irreducibility gives a positive off-diagonal entry in some power
  have hnonneg : ∀ i j, 0 ≤ (N.weightedAdjacencyMatrix κ x) i j :=
    N.weightedAdjacencyMatrix_nonneg κ hx
  have hm : ∀ i j, ∃ k > 0, 0 < (N.weightedAdjacencyMatrix κ x ^ k) i j :=
    (Matrix.isIrreducible_iff_exists_pow_pos hnonneg).mp hirr
  have hne : Nontrivial N.ComplexIdx := by
    by_contra hc
    have h1 : ∀ a b : N.ComplexIdx, a = b := by
      intro a b
      by_contra hne
      exact hc ⟨a, b, hne⟩
    have h2 : Fintype.card N.ComplexIdx ≤ 1 := (Fintype.card_le_one_iff).mpr h1
    omega
  obtain ⟨c, d, hcd⟩ := exists_pair_ne N.ComplexIdx
  obtain ⟨k, hk, hpos⟩ := hm c d
  have h1 : (N.weightedAdjacencyMatrix κ x ^ k) c d = 0 :=
    pow_apply_eq_zero_of_ne (N.weightedAdjacencyMatrix κ x) hdiag k c d hcd
  exact absurd hpos (by rw [h1]; exact lt_irrefl _)

end Network
end CRNT

/-! ### A concrete instance: the self-loop network `A → A`

The self-loop network of `CRNT.Examples.NilpotentJacobian` is the instance in which the
Perron--Frobenius step is not vacuous: its monomial-weighted adjacency matrix is the positive
`1 × 1` matrix `[k]`, which is primitive (and irreducible), while its mass-action Jacobian is the
zero matrix, hence nilpotent.  This is the counterexample to the naive form of the classical
criterion "a primitive weighted adjacency matrix rules out a nilpotent Jacobian": the primitivity
of the weighted adjacency matrix alone does not do it, and the theorem
`CRNT.Network.not_isNilpotentJacobian_of_isPrimitive` therefore needs the additional hypothesis
that the network has at least two complexes (equivalently, that the network is not a single
self-loop). -/

namespace CRNT.Examples.NilpotentJacobian

open CRNT

/-- The complex index type of the self-loop network has a single element. -/
theorem complexIdx_subsingleton : Subsingleton N.ComplexIdx := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  have ha' : a.val = cA := by
    simpa only [complexes_eq, Finset.mem_singleton] using a.property
  have hb' : b.val = cA := by
    simpa only [complexes_eq, Finset.mem_singleton] using b.property
  exact ha'.trans hb'.symm

/-- The source and the target complex of the single reaction coincide. -/
theorem sourceIdx_eq_targetIdx : N.sourceIdx r0 = N.targetIdx r0 := by
  apply Subtype.ext
  simp [Network.sourceIdx, Network.targetIdx, N, rxn, r0]

/-- **The monomial of the complex `A` at `x` is `x 0`.** -/
theorem monomial_eq (x : Concentration Species) : cA.massActionMonomial x = x 0 := by
  simp [Complex.massActionMonomial, cA]

/-- **The weighted adjacency matrix of the self-loop network is strictly positive.**  Its
`(c, d)` entry is the weighted inflow from `d` to `c`; the single reaction is a self-loop with
positive rate, and the network has a single complex, so the entry is positive. -/
theorem weightedAdjacencyMatrix_pos (k : ℝ) (hk : 0 < k) {x : Concentration Species}
    (hx : x.Positive) (c d : N.ComplexIdx) :
    0 < (N.weightedAdjacencyMatrix (rates k hk) x) c d := by
  classical
  let r0' : N.R := r0
  have hsub : Subsingleton N.ComplexIdx := complexIdx_subsingleton
  have hsrc : N.sourceIdx r0' = d := Subsingleton.elim _ _
  have htg : N.targetIdx r0' = c := Subsingleton.elim _ _
  have hsingle : (if N.sourceIdx r0' = d then
        (if N.targetIdx r0' = c then (rates k hk).k r0' *
          N.complexMonomialVector x (N.sourceIdx r0') else 0) else 0)
      ≤ N.weightedAdjacencyMatrix (rates k hk) x c d := by
    unfold Network.weightedAdjacencyMatrix
    refine Finset.single_le_sum
      (f := fun i => (if N.sourceIdx i = d then
        (if N.targetIdx i = c then (rates k hk).k i *
          N.complexMonomialVector x (N.sourceIdx i) else 0) else 0))
      (s := (Finset.univ : Finset N.R)) (fun i _ => ?_) (Finset.mem_univ r0')
    by_cases h1 : N.sourceIdx i = d
    · by_cases h2 : N.targetIdx i = c
      · simp only [ite_eq_left h1, ite_eq_left h2]
        exact mul_nonneg ((rates k hk).positive i).le (N.complexMonomialVector_pos hx _).le
      · simp only [ite_eq_left h1, ite_eq_right h2]
        exact le_rfl
    · simp only [ite_eq_right h1]
      exact le_rfl
  rw [ite_eq_left hsrc, ite_eq_left htg] at hsingle
  have hk0 : 0 < (rates k hk).k r0' := by
    simp [rates]
    linarith
  have hmono : 0 < N.complexMonomialVector x (N.sourceIdx r0') :=
    N.complexMonomialVector_pos hx _
  have hprod : 0 < (rates k hk).k r0' * N.complexMonomialVector x (N.sourceIdx r0') :=
    mul_pos hk0 hmono
  linarith

/-- **The weighted adjacency matrix of the self-loop network is primitive** (and irreducible):
it is the positive `1 × 1` matrix `[k]`. -/
theorem isPrimitive_weightedAdjacencyMatrix (k : ℝ) (hk : 0 < k) :
    Matrix.IsPrimitive (N.weightedAdjacencyMatrix (rates k hk) (fun _ => 1)) := by
  classical
  refine ⟨?_, 1, by omega, ?_⟩
  · intro c d
    exact (weightedAdjacencyMatrix_pos k hk (by intro s; simp) c d).le
  · intro c d
    rw [pow_one]
    exact weightedAdjacencyMatrix_pos k hk (by intro s; simp) c d

/-- **The Perron--Frobenius step, applied to the self-loop network.**  Its weighted adjacency
matrix is primitive, hence not nilpotent. -/
theorem not_isNilpotent_weightedAdjacencyMatrix (k : ℝ) (hk : 0 < k) :
    ¬ IsNilpotent (N.weightedAdjacencyMatrix (rates k hk) (fun _ => 1)) := by
  have hne : Nonempty N.ComplexIdx :=
    ⟨⟨cA, by simp only [complexes_eq, Finset.mem_singleton]⟩⟩
  exact N.not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive (rates k hk)
    (by intro s; simp) hne (isPrimitive_weightedAdjacencyMatrix k hk)

/-- **Primitivity of the weighted adjacency matrix does not, by itself, rule out a nilpotent
Jacobian.**  The self-loop network `A → A` has a primitive weighted adjacency matrix and a
nilpotent mass-action Jacobian at the complex-balanced equilibrium `x* = 1`.

This is why the classical conclusion "the nilpotent-Jacobian criterion cannot apply to a network
with a primitive weighted adjacency matrix" needs the additional hypothesis that the network is
not a single self-loop; see `CRNT.Network.not_isNilpotentJacobian_of_isPrimitive`. -/
theorem isPrimitive_weightedAdjacencyMatrix_of_isNilpotentJacobian (k : ℝ) (hk : 0 < k) :
    Matrix.IsPrimitive (N.weightedAdjacencyMatrix (rates k hk) (fun _ => 1)) ∧
      Network.IsNilpotentJacobian N (rates k hk) (fun _ => 1) :=
  ⟨isPrimitive_weightedAdjacencyMatrix k hk, isNilpotentJacobian k hk _⟩

end CRNT.Examples.NilpotentJacobian

/-! ## Axioms

The principal declarations of this module use only the three standard axioms of Lean's logic
(`propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms CRNT.Network.isNilpotent_massActionJacobian_iff_eigenvalues_zero
#print axioms CRNT.Network.isNilpotent_complexSpaceOperator_iff_eigenvalues_zero
#print axioms CRNT.Network.isNilpotent_iff_eigenvalues_zero
#print axioms CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive
#print axioms CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isIrreducible
#print axioms CRNT.Network.not_isNilpotentJacobian_of_isPrimitive
#print axioms CRNT.Network.not_isNilpotentJacobian_of_isIrreducible
#print axioms CRNT.Examples.NilpotentJacobian.isPrimitive_weightedAdjacencyMatrix
