import CRNT.Oscillation.SpectralOpenness
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Algebra.Polynomial

/-!
# Persistence of distinct negative real spectrum

A key finite-dimensional lemma for Fisher--Fuller stabilization.  If a real monic polynomial has
`n` distinct real roots and all but possibly one are strictly negative, then sufficiently small
real coefficient perturbations still have one simple real root near each old root.  When the
remaining root is centered at zero, positivity of the perturbed constant term pushes it to the
negative side as well.

The proof uses only Mathlib's quantitative continuity-of-roots theorem and counting.  Choose
pairwise disjoint conjugation-invariant disks around the distinct real roots.  Root continuity
produces at least one perturbed root in each disk.  There are exactly `n` roots counting
multiplicity, so each disk contains exactly one simple root and there are no roots elsewhere.
Since the coefficients remain real, conjugation preserves roots and each disk, hence uniqueness
forces every selected root to be real.
-/

namespace Polynomial

open Complex Filter Topology

/-- A monic real polynomial with a complete list of distinct negative real roots. -/
structure SimpleNegativeRealRoots (p : Polynomial ℝ) : Type where
  roots : Multiset ℝ
  card_roots : roots.card = p.natDegree
  nodup : roots.Nodup
  negative : ∀ r ∈ roots, r < 0
  factorization : p = (roots.map (fun r => X - C r)).prod

namespace SimpleNegativeRealRoots

/-- Such a polynomial is monic. -/
theorem monic {p : Polynomial ℝ} (h : SimpleNegativeRealRoots p) : p.Monic := by
  rw [h.factorization]
  exact monic_multiset_prod_of_monic _ _ (by
    intro r hr
    exact monic_X_sub_C r)

/-- No listed root is zero. -/
theorem zero_not_mem {p : Polynomial ℝ} (h : SimpleNegativeRealRoots p) : 0 ∉ h.roots := by
  intro hz
  linarith [h.negative 0 hz]

/-- Adjoin the simple root zero. -/
def consZero {p : Polynomial ℝ} (h : SimpleNegativeRealRoots p) :
    Multiset ℝ := 0 ::ₘ h.roots

/-- The zero-extended root list is distinct. -/
theorem consZero_nodup {p : Polynomial ℝ} (h : SimpleNegativeRealRoots p) :
    h.consZero.Nodup := by
  simp [consZero, h.nodup, h.zero_not_mem]

end SimpleNegativeRealRoots

/-- Minimum geometric separation radius for a finite nodup real root list.  The extra distances to
zero are included so a list of strictly negative roots receives balls contained in the left half
plane. -/
noncomputable def rootIsolationRadius (rs : Multiset ℝ) : ℝ :=
  if h : rs = 0 then 1 else
    (Finset.univ : Finset {r // r ∈ rs}).inf'
      (by
        obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero h
        exact ⟨⟨r, hr⟩, Finset.mem_univ _⟩)
      (fun r => min (-r.1 / 3)
        (if hsingle : (Finset.univ.erase r : Finset {x // x ∈ rs}) = ∅ then 1 else
          (Finset.univ.erase r).inf' (Finset.nonempty_iff_ne_empty.mpr hsingle)
            (fun s => |r.1 - s.1| / 3)))

/-- For a nonempty nodup list of strictly negative roots, the isolation radius is positive. -/
theorem rootIsolationRadius_pos {rs : Multiset ℝ}
    (hne : rs ≠ 0) (hnodup : rs.Nodup) (hneg : ∀ r ∈ rs, r < 0) :
    0 < rootIsolationRadius rs := by
  classical
  rw [rootIsolationRadius, dif_neg hne]
  rw [Finset.lt_inf'_iff]
  intro r hr
  apply lt_min
  · linarith [hneg r.1 r.2]
  ·
    split_ifs with hsingle
    · norm_num
    ·
      rw [Finset.lt_inf'_iff]
      intro s hs
      have hrs : r.1 ≠ s.1 := by
        intro heq
        have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
        exact hsr (Subtype.ext heq).symm
      have : 0 < |r.1 - s.1| := abs_pos.mpr (sub_ne_zero.mpr hrs)
      linarith

/-- A disk around a real center is invariant under complex conjugation. -/
theorem norm_conj_sub_real (z : ℂ) (r : ℝ) :
    ‖star z - (r : ℂ)‖ = ‖z - (r : ℂ)‖ := by
  have hstar : star (z - (r : ℂ)) = star z - (r : ℂ) := by simp
  rw [← hstar, norm_star]

/-- Distinct centers with radius below one third of their separation have disjoint open balls. -/
theorem disjoint_ball_of_dist_three_radius {r s ρ : ℝ}
    (hrs : 3 * ρ ≤ |r - s|) :
    Disjoint (Metric.ball (r : ℂ) ρ) (Metric.ball (s : ℂ) ρ) := by
  rw [Set.disjoint_left]
  intro z hzr hzs
  have htri : ‖(r : ℂ) - (s : ℂ)‖ ≤ ‖(r : ℂ) - z‖ + ‖z - (s : ℂ)‖ :=
    by
      calc
        ‖(r : ℂ) - (s : ℂ)‖ = ‖((r : ℂ) - z) + (z - (s : ℂ))‖ := by congr 1 <;> abel
        _ ≤ _ := norm_add_le _ _
  have hrz : ‖(r : ℂ) - z‖ < ρ := by
    simpa [dist_eq_norm, norm_sub_rev] using hzr
  have hzs' : ‖z - (s : ℂ)‖ < ρ := by simpa [dist_eq_norm] using hzs
  have hnorm : ‖(r : ℂ) - (s : ℂ)‖ = |r - s| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at htri
  nlinarith [norm_nonneg ((r : ℂ) - z)]

/-- A real polynomial's complex root multiset is conjugation-invariant. -/
theorem conj_mem_roots_map_real {p : Polynomial ℝ} {z : ℂ}
    (hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots) :
    star z ∈ (p.map (algebraMap ℝ ℂ)).roots := by
  have hp0 : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro h
    have hmap : p.map (algebraMap ℝ ℂ) = (0 : Polynomial ℝ).map (algebraMap ℝ ℂ) := by
      simpa using h
    have hp : p = 0 := (Polynomial.map_injective (algebraMap ℝ ℂ)
      (RingHom.injective (algebraMap ℝ ℂ))) hmap
    subst p
    simp at hz
  rw [Polynomial.mem_roots hp0] at hz ⊢
  have hz' : Polynomial.eval₂ (algebraMap ℝ ℂ) z p = 0 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hz
  change (p.map (algebraMap ℝ ℂ)).eval (star z) = 0
  rw [← Polynomial.eval₂_eq_eval_map]
  have hstarEval : Polynomial.eval₂ (algebraMap ℝ ℂ) (star z) p =
      star (Polynomial.eval₂ (algebraMap ℝ ℂ) z p) := by
    rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range]
    simp
  simpa [hz'] using hstarEval


/-- Uniform coefficient closeness follows from pointwise coefficient continuity because only
finitely many coefficients up to the fixed degree can be nonzero. -/
theorem eventually_all_coeff_close_of_finite_degree
    {p : Polynomial ℝ} {q : ℝ → Polynomial ℝ}
    (hq0 : q 0 = p)
    (hqdeg : ∀ t, (q t).natDegree = p.natDegree)
    (hcoeff : ∀ k, ContinuousAt (fun t => (q t).coeff k) 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 0, ∀ k, ‖(q t).coeff k - p.coeff k‖ < ε := by
  have hfinite : ∀ᶠ t in 𝓝 0, ∀ k ∈ Finset.range (p.natDegree + 1),
      ‖(q t).coeff k - p.coeff k‖ < ε := by
    have hsubtype : ∀ᶠ t in 𝓝 0, ∀ k : {k // k ∈ Finset.range (p.natDegree + 1)},
        ‖(q t).coeff k - p.coeff k‖ < ε := by
      rw [Filter.eventually_all]
      intro k
      have hkcont : ContinuousAt (fun t => (q t).coeff k.1 - p.coeff k.1) 0 :=
        (hcoeff k.1).sub continuousAt_const
      have hkzero : (q 0).coeff k.1 - p.coeff k.1 = 0 := by
        simp [hq0]
      have hball := hkcont.eventually (Metric.ball_mem_nhds
        ((q 0).coeff k.1 - p.coeff k.1) hε)
      simpa [Real.dist_eq, hkzero] using hball
    filter_upwards [hsubtype] with t ht
    intro k hk
    exact ht ⟨k, hk⟩
  filter_upwards [hfinite] with t ht k
  by_cases hk : k ≤ p.natDegree
  · exact ht k (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))
  · have hp0 : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk)
    have hq0 : (q t).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa [hqdeg t] using lt_of_not_ge hk
    simp [hp0, hq0, hε]

/-- Any radius selected by `rootIsolationRadius` is at most one third of the distance from a
negative root to zero. -/
theorem rootIsolationRadius_le_neg_third
    {p : Polynomial ℝ} (h : SimpleNegativeRealRoots p)
    {r : ℝ} (hr : r ∈ h.roots) :
    rootIsolationRadius h.roots ≤ -r / 3 := by
  classical
  have hne : h.roots ≠ 0 := by intro hz; simpa [hz] using hr
  rw [rootIsolationRadius, dif_neg hne]
  have hbound := Finset.inf'_le
    (fun a : {x // x ∈ h.roots} => min (-a.1 / 3)
      (if hsingle : (Finset.univ.erase a : Finset {x // x ∈ h.roots}) = ∅ then 1 else
        (Finset.univ.erase a).inf' (Finset.nonempty_iff_ne_empty.mpr hsingle)
          (fun b => |a.1 - b.1| / 3)))
    (show (⟨r, hr⟩ : {x // x ∈ h.roots}) ∈ Finset.univ by simp)
  exact hbound.trans (min_le_left _ _)

/-- Distinct listed roots are separated by at least three times the isolation radius. -/
theorem root_ball_separation_le
    (rs : Multiset ℝ) (hnodup : rs.Nodup)
    {ρ : ℝ} (hρ : ρ ≤ rootIsolationRadius rs)
    {r s : {x // x ∈ rs}} (hrs : r ≠ s) :
    3 * ρ ≤ |r.1 - s.1| := by
  classical
  have hne : rs ≠ 0 := by
    intro hz; simpa [hz] using r.2
  have hsErase : s ∈ (Finset.univ : Finset {x // x ∈ rs}).erase r := by
    simp [hrs.symm]
  have huniv : (Finset.univ : Finset {x // x ∈ rs}).Nonempty := by
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩
  rw [rootIsolationRadius, dif_neg hne] at hρ
  have hρr := (Finset.le_inf'_iff huniv _).mp hρ r (Finset.mem_univ _)
  have hinnerNonempty : (Finset.univ.erase r : Finset {x // x ∈ rs}) ≠ ∅ :=
    Finset.ne_empty_of_mem hsErase
  have hinnerCond := (le_min_iff.mp hρr).2
  have hinnerBound : ρ ≤ (Finset.univ.erase r).inf'
      (Finset.nonempty_iff_ne_empty.mpr hinnerNonempty)
      (fun s => |r.1 - s.1| / 3) := by
    split_ifs at hinnerCond with hsingle
    · exact False.elim (hinnerNonempty hsingle)
    · exact hinnerCond
  have hρs := (Finset.le_inf'_iff (Finset.nonempty_iff_ne_empty.mpr hinnerNonempty) _).mp
    hinnerBound s hsErase
  have : ρ ≤ |r.1 - s.1| / 3 := hρs
  linarith

/-- Finite counting lemma used in root continuation: an injective choice of one root in each of
`N` pairwise-disjoint balls exhausts a degree-`N` root multiset. -/
theorem finite_root_balls_exhaust_of_injection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Multiset ℂ} {center rootAt : ι → ℂ} {ρ : ℝ}
    (hroot : ∀ i, rootAt i ∈ R)
    (hnear : ∀ i, ‖rootAt i - center i‖ < ρ)
    (hinj : Function.Injective rootAt)
    (hcard : R.card = Fintype.card ι)
    (hsep : ∀ i j, i ≠ j → 2 * ρ ≤ ‖center i - center j‖) :
    (∀ z ∈ R, ∃ i : ι, z = rootAt i) ∧
      ∀ z ∈ R, ∃! i : ι, ‖z - center i‖ < ρ := by
  classical
  let selected : Multiset ℂ := Multiset.map rootAt (Finset.univ : Finset ι).val
  have hselectedNodup : selected.Nodup := by
    apply Multiset.Nodup.map hinj
    exact Finset.univ.nodup
  have hselected : selected ≤ R := by
    -- Every selected value is a root; injectivity means it is requested only once.
    rw [Multiset.le_iff_count]
    intro z
    by_cases hz : z ∈ selected
    · have hcountsel : Multiset.count z selected = 1 := by
        have hpos := Multiset.count_pos.mpr hz
        have hle := (Multiset.nodup_iff_count_le_one.mp hselectedNodup) z
        omega
      rw [hcountsel]
      have : z ∈ R := by
        obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hz
        rw [← hi]
        exact hroot i
      exact Nat.succ_le_of_lt (Multiset.count_pos.mpr this)
    · simp [Multiset.count_eq_zero.mpr hz]
  have heq : selected = R := by
    apply Multiset.eq_of_le_of_card_le hselected
    simpa [selected, Multiset.card_map, hcard]
  constructor
  · intro z hz
    rw [← heq] at hz
    obtain ⟨i, hi, hiz⟩ := Multiset.mem_map.mp hz
    exact ⟨i, hiz.symm⟩
  · intro z hz
    rw [← heq] at hz
    obtain ⟨i, hi, hiz⟩ := Multiset.mem_map.mp hz
    refine ⟨i, by simpa [hiz] using hnear i, ?_⟩
    intro j hj
    by_contra hij
    have htri : ‖center i - center j‖ ≤
        ‖center i - z‖ + ‖z - center j‖ := by
      calc
        ‖center i - center j‖ = ‖(center i - z) + (z - center j)‖ := by congr 1 <;> abel
        _ ≤ _ := norm_add_le _ _
    have hi' : ‖center i - z‖ < ρ := by simpa [hiz, norm_sub_rev] using hnear i
    linarith [hsep i j (by intro heq; exact hij heq.symm), hi', hj]

/-- One coefficient tolerance controls the quantitative root error at every center in a finite
root list. -/
theorem exists_coeff_tolerance_rootError_lt_on_roots {N : ℕ} (hN : 0 < N)
    (rs : Multiset ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ rs, Matrix.rootErrorBound N ε (r : ℂ) < ρ := by
  classical
  let ι := {r // r ∈ rs}
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ r : ι, Matrix.rootErrorBound N ε (r.1 : ℂ) < ρ := by
    rw [Filter.eventually_all]
    intro r
    exact (Matrix.rootErrorBound_tendsto_zero hN (r.1 : ℂ)).eventually
      (Iio_mem_nhds hρ)
  obtain ⟨ε, hεevent, hεpos⟩ := (hevent.and self_mem_nhdsWithin).exists
  refine ⟨ε, by simpa using hεpos, ?_⟩
  intro r hr
  exact hεevent ⟨r, hr⟩

/-- Quantitative persistence theorem for a finite list of distinct real roots.  The conclusion is
stated as an exact root bijection rather than merely existence of nearby roots. -/
theorem eventually_root_bijection_near_distinct_real
    {p : Polynomial ℝ} (hp : p.Monic)
    (rs : Multiset ℝ) (hcard : rs.card = p.natDegree)
    (hnodup : rs.Nodup)
    (hfactor : p = (rs.map (fun r => X - C r)).prod)
    {q : ℝ → Polynomial ℝ}
    (hqmonic : ∀ t, (q t).Monic)
    (hqdeg : ∀ t, (q t).natDegree = p.natDegree)
    (hq0 : q 0 = p)
    (hcoeff : ∀ k, ContinuousAt (fun t => (q t).coeff k) 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t in 𝓝 0,
        ∃ rootAt : {r // r ∈ rs} → ℂ,
          (∀ r, rootAt r ∈ ((q t).map (algebraMap ℝ ℂ)).roots) ∧
          (∀ r, ‖rootAt r - (r.1 : ℂ)‖ < ρ) ∧
          Function.Injective rootAt ∧
          (∀ r s : {r // r ∈ rs}, r ≠ s → 4 * ρ ≤ |r.1 - s.1|) ∧
          (∀ z ∈ ((q t).map (algebraMap ℝ ℂ)).roots, ∃ r, z = rootAt r) ∧
          ∀ z ∈ ((q t).map (algebraMap ℝ ℂ)).roots,
            ∃! r : {r // r ∈ rs}, ‖z - (r.1 : ℂ)‖ < ρ := by
  classical
  -- Choose a radius smaller than every pairwise separation.  For an empty list the statement is
  -- trivial; the Fisher--Fuller use is always nonempty after the base case.
  by_cases hrs0 : rs = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards with t
    have hdeg0 : (q t).natDegree = 0 := by simpa [hrs0] using (hqdeg t).trans hcard.symm
    have hroots0 : ((q t).map (algebraMap ℝ ℂ)).roots = 0 := by
      exact (Multiset.card_eq_zero).mp (by
        simpa [hdeg0] using Polynomial.card_roots' ((q t).map (algebraMap ℝ ℂ)))
    refine ⟨fun r => False.elim (by simpa [hrs0] using r.2), ?_, ?_, ?_, ?_⟩
    · intro r; exact False.elim (by simpa [hrs0] using r.2)
    · intro r; exact False.elim (by simpa [hrs0] using r.2)
    · intro a; exact False.elim (by simpa [hrs0] using a.2)
    · constructor
      · intro r s hrs; exact False.elim (by simpa [hrs0] using r.2)
      · constructor
        · intro z hz; simp [hroots0] at hz
        · intro z hz; simp [hroots0] at hz
  · let ρ : ℝ :=
      (Finset.univ : Finset {r // r ∈ rs}).inf'
        (by
          obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hrs0
          exact ⟨⟨r, hr⟩, Finset.mem_univ _⟩)
        (fun r =>
          if hsingle : (Finset.univ.erase r : Finset {x // x ∈ rs}) = ∅ then 1 else
            (Finset.univ.erase r).inf' (Finset.nonempty_iff_ne_empty.mpr hsingle)
              (fun s => |r.1 - s.1| / 4))
    have hρ : 0 < ρ := by
      rw [Finset.lt_inf'_iff]
      intro r hr
      split_ifs with hsingle
      · norm_num
      ·
        rw [Finset.lt_inf'_iff]
        intro s hs
        have hrs : r.1 ≠ s.1 := by
          intro heq
          have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
          exact hsr (Subtype.ext heq).symm
        have hdist : 0 < |r.1 - s.1| := abs_pos.mpr (sub_ne_zero.mpr hrs)
        positivity
    have hcenterSep : ∀ r s : {r // r ∈ rs}, r ≠ s →
        4 * ρ ≤ |r.1 - s.1| := by
      intro r s hrs
      have hsErase : s ∈ (Finset.univ.erase r : Finset {x // x ∈ rs}) := by
        simp [hrs.symm]
      have hnotempty : (Finset.univ.erase r : Finset {x // x ∈ rs}) ≠ ∅ :=
        Finset.ne_empty_of_mem hsErase
      have hρr : ρ ≤ if hsingle : (Finset.univ.erase r : Finset {x // x ∈ rs}) = ∅ then 1 else
          (Finset.univ.erase r).inf' (Finset.nonempty_iff_ne_empty.mpr hnotempty)
            (fun b : {x // x ∈ rs} => |r.1 - b.1| / 4) := by
        dsimp [ρ]
        exact Finset.inf'_le _ (Finset.mem_univ r)
      have hinnerBound : ρ ≤ (Finset.univ.erase r).inf'
          (Finset.nonempty_iff_ne_empty.mpr hnotempty)
          (fun b : {x // x ∈ rs} => |r.1 - b.1| / 4) := by
        split_ifs at hρr with hsingle
        · exact False.elim (hnotempty hsingle)
        · exact hρr
      have hρs := (Finset.le_inf'_iff
        (Finset.nonempty_iff_ne_empty.mpr hnotempty)
        (fun b : {x // x ∈ rs} => |r.1 - b.1| / 4)).mp hinnerBound s hsErase
      linarith [hρs]
    -- Turn root-approximation error `< ρ` into a single coefficient tolerance, then use continuity
    -- of the finitely many relevant coefficients.
    have hN : 0 < p.natDegree := by simpa [hcard] using (Multiset.card_pos.mpr hrs0)
    obtain ⟨ε, hε, herr⟩ := exists_coeff_tolerance_rootError_lt_on_roots hN rs hρ
    have hevcoeff : ∀ᶠ t in 𝓝 0, ∀ k, ‖(q t).coeff k - p.coeff k‖ < ε := by
      exact eventually_all_coeff_close_of_finite_degree hq0 hqdeg hcoeff hε
    refine ⟨ρ, hρ, ?_⟩
    filter_upwards [hevcoeff] with t ht
    -- Every base root produces a perturbed root in its own disjoint ball.
    choose rootAt hrootAt hnearErr using fun r : {r // r ∈ rs} => by
      have hbase : p.aeval (r.1 : ℂ) = 0 := by
        rw [Polynomial.aeval_def, hfactor, Polynomial.eval₂_multiset_prod]
        apply Multiset.prod_eq_zero_iff.mpr
        exact Multiset.mem_map.mpr ⟨Polynomial.X - Polynomial.C r.1,
          Multiset.mem_map.mpr ⟨r.1, r.2, rfl⟩, by simp⟩
      exact Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        (a := (r.1 : ℂ)) hε hbase hp (hqmonic t) (by simpa [hqdeg t]) ht
        (Complex.isAlgClosed.splits ((q t).map (algebraMap ℝ ℂ)))
    have hnear : ∀ r : {r // r ∈ rs}, ‖rootAt r - (r.1 : ℂ)‖ < ρ := by
      intro r
      have hraw := hnearErr r
      have hraw' : ‖rootAt r - (r.1 : ℂ)‖ <
          Matrix.rootErrorBound p.natDegree ε (r.1 : ℂ) := by
        simpa [norm_sub_rev, Matrix.rootErrorBound] using hraw
      exact hraw'.trans (herr r.1 r.2)
    have hinj : Function.Injective rootAt := by
      intro r s hrsame
      by_contra hrs
      have hsep := hcenterSep r s hrs
      have htri : |r.1 - s.1| ≤ ‖rootAt r - (r.1 : ℂ)‖ + ‖rootAt s - (s.1 : ℂ)‖ := by
        calc
          |r.1 - s.1| = ‖(r.1 : ℂ) - (s.1 : ℂ)‖ := by
            rw [← Complex.ofReal_sub, Complex.norm_real]
            exact (Real.norm_eq_abs _).symm
          _ ≤ ‖(r.1 : ℂ) - rootAt r‖ + ‖rootAt r - (s.1 : ℂ)‖ := by
            have := norm_add_le ((r.1 : ℂ) - rootAt r) (rootAt r - (s.1 : ℂ))
            simpa only [sub_add_sub_cancel] using this
          _ = ‖rootAt r - (r.1 : ℂ)‖ + ‖rootAt s - (s.1 : ℂ)‖ := by
            simp [hrsame, norm_sub_rev]
      linarith [hnear r, hnear s]
    have hsplit : ((q t).map (algebraMap ℝ ℂ)).Splits :=
      Complex.isAlgClosed.splits ((q t).map (algebraMap ℝ ℂ))
    have hcount : (((q t).map (algebraMap ℝ ℂ)).roots).card = rs.card := by
      rw [← hsplit.natDegree_eq_card_roots, Polynomial.natDegree_map]
      simpa [hqdeg t, hcard]
    have hsubcard : Fintype.card {r // r ∈ rs} = rs.card := by
      calc
        Fintype.card {r // r ∈ rs} = Fintype.card {r // r ∈ rs.toFinset} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Multiset.mem_toFinset.symm))
        _ = rs.toFinset.card := Fintype.card_coe _
        _ = rs.card := Multiset.toFinset_card_of_nodup hnodup
    have hcount' : (((q t).map (algebraMap ℝ ℂ)).roots).card =
        Fintype.card {r // r ∈ rs} := hcount.trans hsubcard.symm
    have hsep : ∀ r s : {r // r ∈ rs}, r ≠ s →
        2 * ρ ≤ ‖(r.1 : ℂ) - (s.1 : ℂ)‖ := by
      intro r s hrs
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      linarith [hcenterSep r s hrs]
    have hrootExhaust := finite_root_balls_exhaust_of_injection hrootAt hnear hinj hcount' hsep
    have hsurj : ∀ z ∈ ((q t).map (algebraMap ℝ ℂ)).roots,
        ∃ r : {r // r ∈ rs}, z = rootAt r := hrootExhaust.1
    have hexhaust : ∀ z ∈ ((q t).map (algebraMap ℝ ℂ)).roots,
        ∃! r : {r // r ∈ rs}, ‖z - (r.1 : ℂ)‖ < ρ := hrootExhaust.2
    exact ⟨rootAt, hrootAt, hnear, hinj, hcenterSep, hsurj, hexhaust⟩

/-- Specialization to roots consisting of a distinct negative list plus zero.  For small parameter,
all roots except the one in the zero ball are real and strictly negative; the zero-ball root is
real as well. -/
theorem eventually_roots_real_with_one_near_zero
    {p : Polynomial ℝ} (hneg : SimpleNegativeRealRoots p)
    {q : ℝ → Polynomial ℝ}
    (hqmonic : ∀ t, (q t).Monic)
    (hqdeg : ∀ t, (q t).natDegree = p.natDegree + 1)
    (hzero : q 0 = X * p)
    (hcoeff : ∀ k, ContinuousAt (fun t => (q t).coeff k) 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ t in 𝓝 0,
        ∃ r0 : ℝ,
          r0 ∈ (q t).roots ∧ |r0| < ρ ∧
          (∀ z : ℂ, z ∈ ((q t).map (algebraMap ℝ ℂ)).roots →
            z = (r0 : ℂ) ∨ z.re < 0) := by
  classical
  let rs0 : Multiset ℝ := 0 ::ₘ hneg.roots
  have hrs0nodup : rs0.Nodup := hneg.consZero_nodup
  have hfact : X * p = (rs0.map (fun r => X - C r)).prod := by
    rw [hneg.factorization]
    simp [rs0]
  have hmonic0 : (X * p).Monic := monic_X.mul hneg.monic
  have hcard0 : rs0.card = (X * p).natDegree := by
    rw [natDegree_mul (monic_X.ne_zero) hneg.monic.ne_zero]
    simp [rs0, hneg.card_roots]
    omega
  have hdegXP : (X * p).natDegree = p.natDegree + 1 := by
    rw [natDegree_mul (monic_X.ne_zero) hneg.monic.ne_zero]
    simp
    omega
  obtain ⟨ρ, hρ, hev⟩ := eventually_root_bijection_near_distinct_real
    hmonic0 rs0 hcard0 hrs0nodup hfact hqmonic
    (by intro t; rw [hdegXP]; exact hqdeg t) hzero (by simpa [hzero] using hcoeff)
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hev] with t ht
  obtain ⟨rootAt, hroot, hnear, hinj, hcenterSep, hsurj, hexhaust⟩ := ht
  let z0 := rootAt ⟨0, by simp [rs0]⟩
  have hz0real : z0.im = 0 := by
    have hconjroot := conj_mem_roots_map_real (hroot ⟨0, by simp [rs0]⟩)
    obtain ⟨s, hstarEq⟩ := hsurj (star z0) hconjroot
    obtain ⟨r, hr, huniq⟩ := hexhaust (star z0) hconjroot
    let zeroIdx : {r // r ∈ rs0} := ⟨0, by simp [rs0]⟩
    have hnearconj : ‖star z0 - (0 : ℂ)‖ < ρ := by
      simpa [z0, zeroIdx, norm_conj_sub_real] using hnear zeroIdx
    have hsnear : ‖star z0 - (s.1 : ℂ)‖ < ρ := by
      rw [hstarEq]
      exact hnear s
    have hconj : star z0 = z0 := by
      have hrzero := huniq zeroIdx (by simpa [zeroIdx] using hnearconj)
      have hsr := huniq s hsnear
      have hsZero : s = zeroIdx := hsr.trans hrzero.symm
      simpa [z0, zeroIdx] using hstarEq.trans (congrArg rootAt hsZero)
    exact Complex.conj_eq_iff_im.mp hconj
  let r0 : ℝ := z0.re
  have hz0eq : z0 = (r0 : ℂ) := by apply Complex.ext <;> simp [r0, hz0real]
  refine ⟨r0, ?_, ?_, ?_⟩
  · have hzmap : (r0 : ℂ) ∈ ((q t).map (algebraMap ℝ ℂ)).roots := by
      simpa [z0, hz0eq] using hroot ⟨0, by simp [rs0]⟩
    have heval := (Polynomial.mem_roots_map_of_injective
      (RingHom.injective (algebraMap ℝ ℂ)) (hqmonic t).ne_zero).mp hzmap
    have hevalR : (q t).eval r0 = 0 := by
      apply (RingHom.injective (algebraMap ℝ ℂ))
      rw [← Polynomial.eval₂_at_apply]
      exact heval
    exact (Polynomial.mem_roots (hqmonic t).ne_zero).2 hevalR
  · have := hnear ⟨0, by simp [rs0]⟩
    simpa [z0, hz0eq, Complex.norm_real, Real.norm_eq_abs] using this
  · intro z hz
    obtain ⟨r, hrnear, hruniq⟩ := hexhaust z hz
    by_cases hr0 : r.1 = 0
    · left
      let zeroIdx : {r // r ∈ rs0} := ⟨0, by simp [rs0]⟩
      have hre : r = zeroIdx := Subtype.ext hr0
      rw [hre] at hrnear
      obtain ⟨i, hzi⟩ := hsurj z hz
      have hiNear : ‖z - (i.1 : ℂ)‖ < ρ := by
        rw [hzi]
        exact hnear i
      have hieq := hruniq i hiNear
      have hzeroNear : ‖z - (zeroIdx.1 : ℂ)‖ < ρ := by simpa [zeroIdx] using hrnear
      have hzeroeq := hruniq zeroIdx hzeroNear
      have hieqzero : i = zeroIdx := hieq.trans hzeroeq.symm
      have hzroot : z = rootAt zeroIdx := hzi.trans (congrArg rootAt hieqzero)
      simpa [z0, zeroIdx, hz0eq] using hzroot
    · right
      have hrmem : r.1 ∈ hneg.roots := by
        simpa [rs0, hr0] using r.2
      have hrneg := hneg.negative r.1 hrmem
      let zeroIdx : {r // r ∈ rs0} := ⟨0, by simp [rs0]⟩
      have hrad4 := hcenterSep zeroIdx r (by
        intro heq
        have : (zeroIdx : ℝ) = r.1 := congrArg Subtype.val heq
        exact hr0 (by simpa [zeroIdx] using this.symm))
      have hrad : ρ ≤ -r.1 / 3 := by
        have hrad4' : 4 * ρ ≤ |(0 : ℝ) - r.1| := by simpa [zeroIdx] using hrad4
        have hpos : 0 < (0 : ℝ) - r.1 := by linarith
        have hdist : |(0 : ℝ) - r.1| = -r.1 := by rw [abs_of_pos hpos]; ring
        rw [hdist] at hrad4'
        linarith
      have hreal : z.im = 0 := by
        have hconjroot := conj_mem_roots_map_real hz
        obtain ⟨s, hstarEq⟩ := hsurj (star z) hconjroot
        obtain ⟨u, hu, huuniq⟩ := hexhaust (star z) hconjroot
        have hsameball : ‖star z - (r.1 : ℂ)‖ < ρ := by
          rw [norm_conj_sub_real]
          exact hrnear
        have hur := huuniq r hsameball
        have hsnear : ‖star z - (s.1 : ℂ)‖ < ρ := by
          rw [hstarEq]
          exact hnear s
        have hus := huuniq s hsnear
        have hsEqR : s = r := hus.trans hur.symm
        obtain ⟨j, hzEq⟩ := hsurj z hz
        have hjnear : ‖z - (j.1 : ℂ)‖ < ρ := by rw [hzEq]; exact hnear j
        have hjr := hruniq j hjnear
        have hzroot : z = rootAt r := hzEq.trans (congrArg rootAt hjr)
        have hstarroot : star z = rootAt r := hstarEq.trans (congrArg rootAt hsEqR)
        have : star z = z := hstarroot.trans hzroot.symm
        exact Complex.conj_eq_iff_im.mp this
      have hreclose : |z.re - r.1| < ρ := by
        have hnorm : ‖z - (r.1 : ℂ)‖ = |z.re - r.1| := by
          rw [Complex.norm_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
            Complex.ofReal_re, Complex.ofReal_im, hreal]
          simp only [sub_zero, zero_mul, add_zero]
          have hsq : (z.re - r.1) * (z.re - r.1) = (z.re - r.1) ^ 2 := by ring
          rw [hsq, Real.sqrt_sq_eq_abs]
        simpa [hnorm] using hrnear
      have hupper := (abs_lt.mp hreclose).2
      linarith

end Polynomial

namespace Polynomial

open Complex Filter Topology

/-- Strengthened zero-extension perturbation theorem used by Fisher--Fuller: if the constant term
of the perturbed monic polynomial has the Hurwitz sign, then sufficiently small *positive*
parameters have a complete list of distinct negative real roots. -/
theorem eventually_simpleNegativeRealRoots_of_zeroExtension
    {p : Polynomial ℝ} (hp : SimpleNegativeRealRoots p)
    {q : ℝ → Polynomial ℝ}
    (hqmonic : ∀ t, (q t).Monic)
    (hqdeg : ∀ t, (q t).natDegree = p.natDegree + 1)
    (hzero : q 0 = X * p)
    (hcoeff : ∀ k, ContinuousAt (fun t => (q t).coeff k) 0)
    (hconst : ∀ t, 0 < t → 0 < (q t).coeff 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Nonempty (SimpleNegativeRealRoots (q t)) := by
  classical
  let rs0 : Multiset ℝ := 0 ::ₘ hp.roots
  have hrs0nodup : rs0.Nodup := hp.consZero_nodup
  have hfact : X * p = (rs0.map (fun r => X - C r)).prod := by
    rw [hp.factorization]
    simp [rs0]
  have hmonic0 : (X * p).Monic := monic_X.mul hp.monic
  have hcard0 : rs0.card = (X * p).natDegree := by
    rw [natDegree_mul (monic_X.ne_zero) hp.monic.ne_zero]
    simp [rs0, hp.card_roots]
    omega
  have hdegXP : (X * p).natDegree = p.natDegree + 1 := by
    rw [natDegree_mul (monic_X.ne_zero) hp.monic.ne_zero]
    simp
    omega
  obtain ⟨ρsep, hρsep, hev⟩ := eventually_root_bijection_near_distinct_real
    hmonic0 rs0 hcard0 hrs0nodup hfact hqmonic
    (by intro t; rw [hdegXP]; exact hqdeg t)
    hzero (by simpa [hzero] using hcoeff)
  let ρ := ρsep
  have hρ : 0 < ρ := hρsep
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
  obtain ⟨rootAt, hroot, hnear0, hinj, hcenterSep, hsurj, hexhaust⟩ := ht
  have hnear : ∀ r, ‖rootAt r - (r.1 : ℂ)‖ < ρ := by
    simpa [ρ] using hnear0
  -- Conjugation plus one-root-per-ball makes every selected root real.
  have hreal : ∀ r : {x // x ∈ rs0}, (rootAt r).im = 0 := by
    intro r
    have hcroot := conj_mem_roots_map_real (hroot r)
    have hcnear : ‖star (rootAt r) - (r.1 : ℂ)‖ < ρsep := by
      rw [norm_conj_sub_real]
      exact hnear0 r
    obtain ⟨s, hstarEq⟩ := hsurj (star (rootAt r)) hcroot
    obtain ⟨u, hu, huuniq⟩ := hexhaust (star (rootAt r)) hcroot
    have hsr := huuniq r hcnear
    have hsu : ‖star (rootAt r) - (s.1 : ℂ)‖ < ρsep := by
      rw [hstarEq]
      exact hnear0 s
    have hsu' := huuniq s hsu
    have hsEqR : s = r := hsu'.trans hsr.symm
    have hconj : star (rootAt r) = rootAt r := hstarEq.trans (congrArg rootAt hsEqR)
    exact Complex.conj_eq_iff_im.mp hconj
  let realRoot : {x // x ∈ rs0} → ℝ := fun r => (rootAt r).re
  have hrootEq : ∀ r, rootAt r = (realRoot r : ℂ) := by
    intro r
    apply Complex.ext <;> simp [realRoot, hreal r]
  have hrealInj : Function.Injective realRoot := by
    intro r s hrs
    apply hinj
    rw [hrootEq r, hrootEq s, hrs]
  let rst : Multiset ℝ :=
    Multiset.map realRoot (Finset.univ : Finset {x // x ∈ rs0}).val
  have hrstNodup : rst.Nodup := by
    exact Multiset.Nodup.map hrealInj Finset.univ.nodup
  have hrstCard : rst.card = (q t).natDegree := by
    have hsubcard : Fintype.card {x // x ∈ rs0} = rs0.card := by
      calc
        Fintype.card {x // x ∈ rs0} = Fintype.card {x // x ∈ rs0.toFinset} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Multiset.mem_toFinset.symm))
        _ = rs0.toFinset.card := Fintype.card_coe _
        _ = rs0.card := Multiset.toFinset_card_of_nodup hrs0nodup
    calc
      rst.card = Fintype.card {x // x ∈ rs0} := by simp [rst, Multiset.card_map]
      _ = rs0.card := hsubcard
      _ = (X * p).natDegree := hcard0
      _ = (q t).natDegree := by rw [hdegXP, hqdeg t]
  -- Old negative centers remain negative.
  have hnegOld : ∀ r : {x // x ∈ rs0}, r.1 ≠ 0 → realRoot r < 0 := by
    intro r hr0
    have hrmem : r.1 ∈ hp.roots := by
      simpa [rs0, hr0] using r.2
    have hcenter := hp.negative r.1 hrmem
    let zeroIdx : {x // x ∈ rs0} := ⟨0, by simp [rs0]⟩
    have hrad4 := hcenterSep zeroIdx r (by
      intro heq
      have hval : (zeroIdx : ℝ) = r.1 := congrArg Subtype.val heq
      exact hr0 (by simpa [zeroIdx] using hval.symm))
    have hrad : ρ ≤ -r.1 / 3 := by
      have hrad4' : 4 * ρsep ≤ |(0 : ℝ) - r.1| := by simpa [ρ, zeroIdx] using hrad4
      have hpos : 0 < (0 : ℝ) - r.1 := by linarith
      rw [abs_of_pos hpos] at hrad4'
      linarith
    have hclose : |realRoot r - r.1| < ρ := by
      have hcloseC := hnear r
      rw [hrootEq r, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hcloseC
      exact hcloseC
    have hclose' := (abs_lt.mp hclose).2
    linarith
  -- Since the selected roots exhaust all complex roots and are real, monicity gives the exact real
  -- factorization by `rst`.
  have hfactorT : q t = (rst.map (fun r => X - C r)).prod := by
    apply Polynomial.map_injective _ (RingHom.injective (algebraMap ℝ ℂ))
    have hrootsEq : ((q t).map (algebraMap ℝ ℂ)).roots =
        rst.map (fun r : ℝ => (r : ℂ)) := by
      let selectedC : Multiset ℂ :=
        Multiset.map rootAt (Finset.univ : Finset {x // x ∈ rs0}).val
      have hselectedNodup : selectedC.Nodup := by
        exact Multiset.Nodup.map hinj Finset.univ.nodup
      have hselected : selectedC ≤ ((q t).map (algebraMap ℝ ℂ)).roots := by
        rw [Multiset.le_iff_count]
        intro z
        by_cases hz : z ∈ selectedC
        · have hcount : selectedC.count z = 1 := by
            have hpos := Multiset.count_pos.mpr hz
            have hle := (Multiset.nodup_iff_count_le_one.mp hselectedNodup) z
            omega
          rw [hcount]
          apply Nat.succ_le_of_lt (Multiset.count_pos.mpr ?_)
          obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
          exact hroot i
        · simp [Multiset.count_eq_zero.mpr hz]
      have hselectedCard : selectedC.card =
          (((q t).map (algebraMap ℝ ℂ)).roots).card := by
        rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
        have hsubcard : Fintype.card {x // x ∈ rs0} = rs0.card := by
          calc
            Fintype.card {x // x ∈ rs0} = Fintype.card {x // x ∈ rs0.toFinset} :=
              Fintype.card_congr (Equiv.subtypeEquivRight
                (fun _ => Multiset.mem_toFinset.symm))
            _ = rs0.toFinset.card := Fintype.card_coe _
            _ = rs0.card := Multiset.toFinset_card_of_nodup hrs0nodup
        calc
          selectedC.card = Fintype.card {x // x ∈ rs0} := by
            simp [selectedC, Multiset.card_map]
          _ = rs0.card := hsubcard
          _ = (X * p).natDegree := hcard0
          _ = (q t).natDegree := by rw [hdegXP, hqdeg t]
      have heq : selectedC = ((q t).map (algebraMap ℝ ℂ)).roots := by
        exact Multiset.eq_of_le_of_card_le hselected (by rw [hselectedCard])
      rw [← heq]
      change Multiset.map rootAt (Finset.univ : Finset {x // x ∈ rs0}).val =
        Multiset.map (fun r : ℝ => (r : ℂ)) rst
      simp only [rst, Multiset.map_map, Function.comp_def]
      refine Multiset.map_congr rfl ?_
      intro i hi
      exact hrootEq i
    have hsplit : ((q t).map (algebraMap ℝ ℂ)).Splits :=
      Complex.isAlgClosed.splits _
    rw [hsplit.eq_prod_roots_of_monic ((hqmonic t).map (algebraMap ℝ ℂ)), hrootsEq]
    rw [Polynomial.map_multiset_prod]
    simp only [Multiset.map_map, Function.comp_def]
    apply congrArg Multiset.prod
    refine Multiset.map_congr rfl ?_
    intro x hx
    simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  -- The root associated with center zero must also be negative.  Evaluate the factorization at zero:
  -- the constant term is positive, every old-root factor contributes a positive number, hence the
  -- remaining factor `-r0` is positive.
  have hzeroMem : (0 : ℝ) ∈ rs0 := by simp [rs0]
  let zidx : {x // x ∈ rs0} := ⟨0, hzeroMem⟩
  have hzneg : realRoot zidx < 0 := by
    have hct : 0 < (q t).coeff 0 := hconst t (by simpa using htpos)
    have hctprod : 0 < (rst.map (fun r => -r)).prod := by
      simpa [hfactorT, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod] using hct
    have hprodOld : 0 < ((rst.erase (realRoot zidx)).map (fun r => -r)).prod := by
      apply Multiset.prod_pos
      intro r hr
      obtain ⟨r', hrErase, rfl⟩ := Multiset.mem_map.mp hr
      have hrstMem : r' ∈
          Multiset.map realRoot (Finset.univ : Finset {x // x ∈ rs0}).val := by
        simpa [rst] using Multiset.mem_of_mem_erase hrErase
      obtain ⟨idx, hidx, hrEq⟩ := Multiset.mem_map.mp hrstMem
      have hneidx : idx ≠ zidx := by
        intro heq
        have hval : r' = realRoot zidx := by rw [← hrEq, heq]
        have hmem : realRoot zidx ∈ rst.erase (realRoot zidx) := by
          simpa [hval] using hrErase
        have hpos := Multiset.count_pos.mpr hmem
        rw [Multiset.count_erase_self] at hpos
        have hcount := (Multiset.nodup_iff_count_le_one.mp hrstNodup) (realRoot zidx)
        omega
      have hcenterne : idx.1 ≠ 0 := by
        intro h0
        apply hneidx
        exact Subtype.ext h0
      have hneg := hnegOld idx hcenterne
      rw [← hrEq]
      linarith
    have hmember : realRoot zidx ∈ rst := by
      change realRoot zidx ∈
        Multiset.map realRoot (Finset.univ : Finset {x // x ∈ rs0}).val
      exact Multiset.mem_map.mpr ⟨zidx, Finset.mem_univ _, rfl⟩
    have hsplit : (rst.map (fun r => -r)).prod = (- realRoot zidx) *
        ((rst.erase (realRoot zidx)).map (fun r => -r)).prod := by
      rw [← Multiset.cons_erase hmember]
      simp
    rw [hsplit] at hctprod
    have hrootNeg : 0 < -realRoot zidx := by
      by_contra hnonpos
      have hnonpos' : -realRoot zidx ≤ 0 := le_of_not_gt hnonpos
      have hmul := mul_nonpos_of_nonpos_of_nonneg hnonpos' (le_of_lt hprodOld)
      linarith
    linarith
  refine ⟨{
    roots := rst
    card_roots := hrstCard
    nodup := hrstNodup
    negative := ?_
    factorization := hfactorT }⟩
  intro r hr
  have hrstMem : r ∈
      Multiset.map realRoot (Finset.univ : Finset {x // x ∈ rs0}).val := by
    simpa [rst] using hr
  obtain ⟨idx, hidx, hrEq⟩ := Multiset.mem_map.mp hrstMem
  rw [← hrEq]
  by_cases hcenter : idx.1 = 0
  · have hidx0 : idx = zidx := Subtype.ext hcenter
    subst hidx0
    simpa using hzneg
  · exact hnegOld idx hcenter

end Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complete simple negative real factorization of the characteristic polynomial implies Hurwitz
stability of the matrix. -/
theorem isHurwitzReal_of_simpleNegativeRealRoots
    {M : Matrix n n ℝ}
    (h : Polynomial.SimpleNegativeRealRoots M.charpoly) : M.IsHurwitzReal := by
  intro z hz
  have hz' : Polynomial.eval₂ (algebraMap ℝ ℂ) z M.charpoly = 0 := by
    have hp0 : (M.map (algebraMap ℝ ℂ)).charpoly ≠ 0 :=
      (Matrix.charpoly_monic (M.map (algebraMap ℝ ℂ))).ne_zero
    have hzroot := (Polynomial.mem_roots hp0).mp hz
    change ((M.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 at hzroot
    rw [Matrix.charpoly_map] at hzroot
    rw [← Polynomial.eval₂_eq_eval_map] at hzroot
    exact hzroot
  rw [h.factorization, Polynomial.eval₂_multiset_prod] at hz'
  have hz'' : (h.roots.map (fun a => Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (Polynomial.X - Polynomial.C a))).prod = 0 := by
    simpa only [Multiset.map_map, Function.comp_def] using hz'
  have hzeroMem : (0 : ℂ) ∈
      h.roots.map (fun a => Polynomial.eval₂ (algebraMap ℝ ℂ) z
        (Polynomial.X - Polynomial.C a)) :=
    Multiset.prod_eq_zero_iff.mp hz''
  obtain ⟨a, ha, heval⟩ := Multiset.mem_map.mp hzeroMem
  have hzsub : z - (a : ℂ) = 0 := by simpa using heval
  have : z = (a : ℂ) := sub_eq_zero.mp hzsub
  simpa [this] using h.negative a ha

end Matrix
