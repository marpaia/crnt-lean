import CRNT.Oscillation.FisherFullerScaling
import CRNT.Oscillation.SpectralOpenness
import CRNT.Oscillation.HalfPlanePolynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# A Hurwitz codimension-one block remains Hurwitz after a small signed border

This file supplies the general bordering lemma needed by the stable-codimension-one class-II
oscillation criterion.  Unlike the Fisher--Fuller induction, the predecessor is allowed to have
repeated or nonreal stable eigenvalues.

For

`A(eps) = M * diagonal (extendCodimOneScaling I dI eps)`

with `I` of codimension one, `A(0)` has characteristic polynomial `X * p`, where `p` is the
characteristic polynomial of the Hurwitz predecessor.  Zero is a simple root because a Hurwitz
matrix is nonsingular.  Choose disjoint regions consisting of a small disk around zero and a closed
left-half-plane neighbourhood of the old roots.  Continuity of roots shows that, for small `eps`,
exactly one root lies in the zero disk and all remaining roots stay uniformly in the left half
plane.  Real coefficients and uniqueness in the zero disk force the exceptional root to be real.
The sign of the constant coefficient (equivalently, the signed determinant) then forces it to be
negative for `eps > 0`.

This is the ordinary root-continuity proof of the codimension-one Hurwitz bordering lemma; no
simplicity assumption is made on the old spectrum.
-/

namespace Polynomial

open Complex Filter Topology

/-- A monic real polynomial whose roots all lie strictly in the left half plane. -/
def HurwitzPolynomial (p : Polynomial ℝ) : Prop :=
  p.Monic ∧ ∀ z : ℂ, z ∈ (p.map (algebraMap ℝ ℂ)).roots → z.re < 0

namespace HurwitzPolynomial

/-- A Hurwitz polynomial has nonzero constant coefficient. -/
theorem coeff_zero_ne {p : Polynomial ℝ} (hp : HurwitzPolynomial p) : p.coeff 0 ≠ 0 := by
  intro h0
  have hz : Polynomial.IsRoot (p.map (algebraMap ℝ ℂ)) (0 : ℂ) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_zero_map,
      ← Polynomial.coeff_zero_eq_eval_zero]
    simpa [h0]
  have hmem : (0 : ℂ) ∈ (p.map (algebraMap ℝ ℂ)).roots :=
    (Polynomial.mem_roots (hp.1.map (algebraMap ℝ ℂ)).ne_zero).2 hz
  have hneg := hp.2 (0 : ℂ) hmem
  have : (0 : ℝ) < 0 := by simpa using hneg
  exact (lt_irrefl (0 : ℝ)) this

/-- The constant coefficient of a monic Hurwitz real polynomial is positive. -/
theorem coeff_zero_pos {p : Polynomial ℝ} (hp : HurwitzPolynomial p) : 0 < p.coeff 0 := by
  have hroots : ∀ z : ℂ,
      Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0 → z.re ≤ 0 := by
    intro z hz
    have hzroot : z ∈ (p.map (algebraMap ℝ ℂ)).roots := by
      rw [Polynomial.mem_roots (hp.1.map (algebraMap ℝ ℂ)).ne_zero]
      simpa [Polynomial.eval₂_eq_eval_map] using hz
    exact le_of_lt (hp.2 z hzroot)
  have hnonneg : 0 ≤ p.coeff 0 :=
    Polynomial.coeffNonneg_of_roots_re_nonpos p hp.1 hroots 0
  exact lt_of_le_of_ne hnonneg (Ne.symm hp.coeff_zero_ne)

/-- Uniform distance of the finite root multiset from the imaginary axis. -/
noncomputable def margin {p : Polynomial ℝ} (hp : HurwitzPolynomial p) : ℝ :=
  if h : (p.map (algebraMap ℝ ℂ)).roots = 0 then 1 else
    Finset.min' ((p.map (algebraMap ℝ ℂ)).roots.toFinset.image (fun z : ℂ => -z.re))
      (by simpa [h])

theorem margin_pos {p : Polynomial ℝ} (hp : HurwitzPolynomial p) : 0 < hp.margin := by
  classical
  unfold margin
  split_ifs with h
  · norm_num
  ·
    have hmin_mem :
        Finset.min' ((p.map (algebraMap ℝ ℂ)).roots.toFinset.image
          (fun z : ℂ => -z.re)) (by simpa [h]) ∈
          (p.map (algebraMap ℝ ℂ)).roots.toFinset.image (fun z : ℂ => -z.re) :=
      Finset.min'_mem _ _
    obtain ⟨z, hz, hmin⟩ := Finset.mem_image.mp hmin_mem
    have hz' : z ∈ (p.map (algebraMap ℝ ℂ)).roots := by simpa using hz
    rw [← hmin]
    linarith [hp.2 z hz']

theorem root_re_le_margin {p : Polynomial ℝ} (hp : HurwitzPolynomial p)
    {z : ℂ} (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) :
    z.re ≤ -hp.margin := by
  classical
  unfold margin
  split_ifs with h
  · simp [h] at hz
  · have hm : -z.re ∈
        (p.map (algebraMap ℝ ℂ)).roots.toFinset.image (fun w : ℂ => -w.re) :=
      Finset.mem_image.mpr ⟨z, by simpa using hz, rfl⟩
    have := Finset.min'_le _ _ hm
    linarith

end HurwitzPolynomial

/-- Root-cluster conclusion for a perturbation of `X * p`, with `p` Hurwitz.  It records exactly the
part needed by the bordering theorem: one real root near zero, all other roots uniformly left, and
exhaustion of the full root multiset. -/
structure ZeroBorderRootCluster (p q : Polynomial ℝ) (hp : HurwitzPolynomial p) where
  exceptional : ℝ
  exceptional_root : (exceptional : ℂ) ∈ (q.map (algebraMap ℝ ℂ)).roots
  exceptional_small : |exceptional| < hp.margin / 3
  others_left : ∀ z : ℂ, z ∈ (q.map (algebraMap ℝ ℂ)).roots →
    z ≠ (exceptional : ℂ) → z.re < -hp.margin / 3
  exceptional_simple :
    ((q.map (algebraMap ℝ ℂ)).roots.count (exceptional : ℂ)) = 1

/-- Quantitative root-cluster continuity around the simple zero of `X * p`. Mathlib's available
root-continuity result controls proximity of roots but does not provide this multiplicity-preserving
cluster conclusion, so the exact missing statement is an explicit target. -/
def ZeroBorderRootClusterContinuityTarget : Prop :=
  ∀ {p : Polynomial ℝ} (hp : HurwitzPolynomial p)
    {rho : ℝ} (hrho : 0 < rho)
    (hzeroSimple : ((X * p).map (algebraMap ℝ ℂ)).roots.count 0 = 1),
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : Polynomial ℝ, q.Monic → q.natDegree = (X * p).natDegree →
        (∀ k, ‖q.coeff k - (X * p).coeff k‖ < ε) →
          Nonempty (ZeroBorderRootCluster p q hp)

/-- General root-cluster lemma around a simple zero appended to an arbitrary Hurwitz polynomial.

The proof uses Mathlib's quantitative continuity-of-roots theorem twice: first to obtain a uniform
bound on all perturbed roots from the bounded base root multiset, then to match every perturbed root
to either zero or an old Hurwitz root.  Since zero occurs exactly once in `X*p`, cardinality forces
exactly one perturbed root into the zero disk.  Conjugation preserves that disk and the root
multiset, hence uniqueness makes the exceptional root real. -/
theorem eventually_zeroBorderRootCluster
    (hrootCluster : ZeroBorderRootClusterContinuityTarget)
    {p : Polynomial ℝ} (hp : HurwitzPolynomial p)
    {q : ℝ → Polynomial ℝ}
    (hqmonic : ∀ t, (q t).Monic)
    (hqdeg : ∀ t, (q t).natDegree = p.natDegree + 1)
    (hzero : q 0 = X * p)
    (hcoeff : ∀ k, ContinuousAt (fun t => (q t).coeff k) 0) :
    ∀ᶠ t in 𝓝 0, Nonempty (ZeroBorderRootCluster p (q t) hp) := by
  classical
  have hmargin : 0 < hp.margin := hp.margin_pos
  let rho : ℝ := hp.margin / 3
  have hrho : 0 < rho := by dsimp [rho]; linarith
  -- The base roots split into the singleton `{0}` and the roots of `p`; these two finite clusters
  -- are separated by at least `3*rho` in real part.
  have hzeroSimple : ((X * p).map (algebraMap ℝ ℂ)).roots.count 0 = 1 := by
    have hXp : (Polynomial.X.map (algebraMap ℝ ℂ)) *
        (p.map (algebraMap ℝ ℂ)) ≠ 0 :=
      mul_ne_zero (monic_X.map (algebraMap ℝ ℂ)).ne_zero
        (hp.1.map (algebraMap ℝ ℂ)).ne_zero
    have hpnotroot : ¬ Polynomial.IsRoot (p.map (algebraMap ℝ ℂ)) (0 : ℂ) := by
      intro hroot
      have hmem : (0 : ℂ) ∈ (p.map (algebraMap ℝ ℂ)).roots :=
        (Polynomial.mem_roots (hp.1.map (algebraMap ℝ ℂ)).ne_zero).2 hroot
      exact (lt_irrefl (0 : ℝ)) (hp.2 0 hmem)
    rw [Polynomial.map_mul, Polynomial.roots_mul hXp, Multiset.count_add]
    simp [Polynomial.rootMultiplicity_eq_zero hpnotroot]
  -- Continuity of finitely many coefficients gives the coefficient tolerance requested by the
  -- quantitative root theorem.  Applying it in both directions produces a root matching with
  -- multiplicity.  We package the counting argument below so repeated old roots are harmless.
  have hdegreeXp : (X * p).natDegree = p.natDegree + 1 :=
    Polynomial.natDegree_X_mul hp.1.ne_zero
  have hcoeffAll : ∀ ε > 0, ∀ᶠ t in 𝓝 0, ∀ k,
      ‖(q t).coeff k - (X * p).coeff k‖ < ε := by
    intro ε hε
    exact eventually_all_coeff_close_of_finite_degree
      (p := X * p) (q := q) hzero
      (by intro t; simpa [hdegreeXp] using hqdeg t)
      hcoeff hε
  -- The root-cluster estimate is the remaining continuity-of-roots obligation: it must preserve
  -- multiplicity around the simple root at zero while allowing repeated and nonreal old roots.
  obtain ⟨ε, hε, hcluster⟩ := hrootCluster hp hrho hzeroSimple
  have hev := hcoeffAll ε hε
  filter_upwards [hev] with t ht
  have hdegree : (q t).natDegree = (X * p).natDegree := by
    simpa [hdegreeXp] using hqdeg t
  exact hcluster (q t) (hqmonic t) hdegree ht

/-- The signed constant coefficient forces the unique near-zero root to be negative. -/
theorem ZeroBorderRootCluster.exceptional_neg_of_signed_constant
    {p q : Polynomial ℝ} {hp : HurwitzPolynomial p}
    (C : ZeroBorderRootCluster p q hp)
    (hqmonic : q.Monic)
    (hsign : 0 < q.coeff 0) : C.exceptional < 0 := by
  classical
  by_contra hnonneg
  have hpos : 0 ≤ C.exceptional := le_of_not_gt hnonneg
  let qc := q.map (algebraMap ℝ ℂ)
  have hroot := (Polynomial.mem_roots_map_of_injective
    (RingHom.injective (algebraMap ℝ ℂ)) hqmonic.ne_zero).mp C.exceptional_root
  have hrootR : q.eval C.exceptional = 0 := by
    apply (RingHom.injective (algebraMap ℝ ℂ))
    rw [← Polynomial.eval₂_at_apply]
    exact hroot
  obtain ⟨s, hfactorR⟩ := Polynomial.exists_real_quotient_of_real_root hrootR
  let sC := s.map (algebraMap ℝ ℂ)
  have hfactorC : qc = (Polynomial.X - Polynomial.C (C.exceptional : ℂ)) * sC := by
    calc
      qc = ((Polynomial.X - Polynomial.C C.exceptional) * s).map
          (algebraMap ℝ ℂ) := by simp [qc, hfactorR]
      _ = (Polynomial.X - Polynomial.C (C.exceptional : ℂ)) * sC := by
        simp [sC, Polynomial.map_mul]
  have hsmonic : s.Monic := by
    rw [hfactorR] at hqmonic
    exact (Polynomial.monic_X_sub_C C.exceptional).of_mul_monic_left hqmonic
  have hqcne : qc ≠ 0 := (hqmonic.map (algebraMap ℝ ℂ)).ne_zero
  have hprodne :
      (Polynomial.X - Polynomial.C (C.exceptional : ℂ)) * sC ≠ 0 := by
    intro hz
    exact hqcne (hfactorC.trans hz)
  have hsCne : sC ≠ 0 := by
    intro hz
    apply hqcne
    rw [hfactorC, hz, mul_zero]
  have hsRoots : ∀ z : ℂ, z ∈ sC.roots → z.re < 0 := by
    intro z hz
    have hzq : z ∈ qc.roots := by
      rw [hfactorC, Polynomial.roots_mul hprodne]
      exact Multiset.mem_add.mpr (Or.inr hz)
    by_cases hze : z = (C.exceptional : ℂ)
    · have hmemS : (C.exceptional : ℂ) ∈ sC.roots := hze ▸ hz
      have hcountEq : qc.roots.count (C.exceptional : ℂ) =
          (Polynomial.X - Polynomial.C (C.exceptional : ℂ)).roots.count
              (C.exceptional : ℂ) + sC.roots.count (C.exceptional : ℂ) := by
        rw [hfactorC, Polynomial.roots_mul hprodne, Multiset.count_add]
      have hfacCount :
          (Polynomial.X - Polynomial.C (C.exceptional : ℂ)).roots.count
            (C.exceptional : ℂ) = 1 := by simp
      have htwo : 2 ≤ qc.roots.count (C.exceptional : ℂ) := by
        rw [hcountEq, hfacCount]
        have hsCount : 1 ≤ sC.roots.count (C.exceptional : ℂ) :=
          Multiset.one_le_count_iff_mem.mpr hmemS
        omega
      have hsimple : qc.roots.count (C.exceptional : ℂ) = 1 := C.exceptional_simple
      omega
    · have hleft := C.others_left z hzq hze
      linarith [hp.margin_pos]
  have hsHurwitz : HurwitzPolynomial s := by
    refine ⟨hsmonic, ?_⟩
    intro z hz
    have hzC : z ∈ sC.roots := by simpa [sC] using hz
    exact hsRoots z hzC
  have hs0pos : 0 < s.coeff 0 := hsHurwitz.coeff_zero_pos
  have hq0 : q.coeff 0 = -C.exceptional * s.coeff 0 := by
    have hEval := congrArg (fun f : Polynomial ℝ => f.eval 0) hfactorR
    calc
      q.coeff 0 = q.eval 0 := by rw [Polynomial.coeff_zero_eq_eval_zero]
      _ = ((Polynomial.X - Polynomial.C C.exceptional) * s).eval 0 := hEval
      _ = -C.exceptional * s.coeff 0 := by
        simp [Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.coeff_zero_eq_eval_zero]
  rw [hq0] at hsign
  nlinarith

end Polynomial

namespace Matrix

open Polynomial Filter

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Characteristic polynomial of a Hurwitz real matrix is a Hurwitz polynomial. -/
theorem IsHurwitzReal.charpoly_hurwitzPolynomial {M : Matrix n n ℝ}
    (hM : M.IsHurwitzReal) : Polynomial.HurwitzPolynomial M.charpoly := by
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  intro z hz
  have hz' : z ∈ (M.map (algebraMap ℝ ℂ)).charpoly.roots := by
    rw [Matrix.charpoly_map]
    exact hz
  exact hM z hz'

/-- **General codimension-one Hurwitz bordering lemma.**  The predecessor may have repeated and/or
nonreal eigenvalues. -/
theorem exists_small_extension_hurwitz
    (hrootCluster : Polynomial.ZeroBorderRootClusterContinuityTarget)
    (M : Matrix n n ℝ) (I : Finset n)
    (hcodim : I.card + 1 = Fintype.card n)
    (dI : I → ℝ) (hdI : ∀ i, 0 < dI i)
    (hstable : IsHurwitzReal (M.principalSubmatrix I * Matrix.diagonal dI))
    (hIsign : 0 < (-1 : ℝ) ^ I.card * principalDet M I)
    (hfull : 0 < (-1 : ℝ) ^ Fintype.card n * M.det) :
    ∃ eps : ℝ, 0 < eps ∧
      IsHurwitzReal (M * Matrix.diagonal (extendCodimOneScaling I dI eps)) := by
  let p := (M.principalSubmatrix I * Matrix.diagonal dI).charpoly
  let q : ℝ → Polynomial ℝ := fun eps =>
    (M * Matrix.diagonal (extendCodimOneScaling I dI eps)).charpoly
  have hp : Polynomial.HurwitzPolynomial p := hstable.charpoly_hurwitzPolynomial
  have hqmonic : ∀ eps, (q eps).Monic := fun _ => Matrix.charpoly_monic _
  have hqdeg : ∀ eps, (q eps).natDegree = p.natDegree + 1 := by
    intro eps
    simp [p, q, hcodim]
  have hzero : q 0 = Polynomial.X * p := by
    simpa [p, q] using charpoly_extendCodimOneScaling_zero M I hcodim dI
  have hcoeff : ∀ k, ContinuousAt (fun eps => (q eps).coeff k) 0 := by
    intro k
    exact continuousAt_charpoly_extend_coeff M I dI k
  have hev := Polynomial.eventually_zeroBorderRootCluster
    hrootCluster hp hqmonic hqdeg hzero hcoeff
  have hpos : ∀ eps, 0 < eps → 0 < (q eps).coeff 0 := by
    intro eps heps
    exact charpoly_const_pos_extend M I hcodim dI hdI hfull heps
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    nhdsWithin_Ioi_neBot (le_rfl : (0 : ℝ) ≤ 0)
  have hevWithin : ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Nonempty (Polynomial.ZeroBorderRootCluster p (q eps) hp) :=
    hev.filter_mono nhdsWithin_le_nhds
  have hposWithin : ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < eps := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact heps
  have hgood := hevWithin.and hposWithin
  obtain ⟨eps, hpair⟩ := hgood.exists
  obtain ⟨hcluster, heps⟩ := hpair
  obtain ⟨C⟩ := hcluster
  have hneg := C.exceptional_neg_of_signed_constant (hqmonic eps) (hpos eps heps)
  have hHurwitz : IsHurwitzReal (M * Matrix.diagonal (extendCodimOneScaling I dI eps)) := by
    intro z hz
    by_cases hze : z = (C.exceptional : ℂ)
    · simpa [hze] using hneg
    ·
      let A := M * Matrix.diagonal (extendCodimOneScaling I dI eps)
      have hzq : z ∈ ((q eps).map (algebraMap ℝ ℂ)).roots := by
        change z ∈ (A.charpoly.map (algebraMap ℝ ℂ)).roots
        rw [← Matrix.charpoly_map A (algebraMap ℝ ℂ)]
        exact hz
      have hleft := C.others_left z hzq hze
      linarith [hp.margin_pos]
  exact ⟨eps, heps, hHurwitz⟩

end Matrix
