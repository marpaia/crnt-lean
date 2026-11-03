import CRNT.Algebra.GroebnerBasis
import Mathlib.Tactic.FieldSimp

/-!
# Buchberger's criterion

For a finite family `G` of nonzero polynomials over a field and a monomial order, the
`S`-polynomial of `G i` and `G j` is
`S(G i, G j) = x^{γ − deg G i} / lc(G i) · G i − x^{γ − deg G j} / lc(G j) · G j`,
`γ = lcm(deg G i, deg G j) = deg G i ⊔ deg G j`. Buchberger's criterion (Cox–Little–O'Shea,
Theorem 2.6.6): `G` is a Gröbner basis of the ideal it generates iff every `S(G i, G j)` has
remainder zero on division by `G`.

The proof follows Cox–Little–O'Shea. Among all representations `f = ∑ h_k G_k` choose one whose
largest degree `δ = max deg(h_k G_k)` is minimal (the order on monomials is well founded). If
`δ > deg f`, the top-degree parts `lt(h_k) G_k` cancel at `δ`; their sum is a combination of
`x^{δ − γ} S(G_k, G_{k₀})` (`k₀` one fixed top index), and representations of the
`S`-polynomials below their `lcm` give a representation with smaller `δ`.

* `sPoly`, `HasLcmRepresentation`.
* `isGroebnerBasis_of_lcmRepresentation`: representations below the `lcm` imply a Gröbner basis.
* `sPoly_degree_lt`: the `S`-polynomial has degree below the `lcm`.
* `hasLcmRepresentation_of_remainder_zero`: a zero remainder gives such a representation.
* `SPolyReducesToZero`, `hasLcmRepresentation_of_reducesToZero`.
* `isGroebnerBasis_iff_remainders_zero`: **Buchberger's criterion.**
-/

namespace CRNT

namespace Groebner

open MvPolynomial MonomialOrder

variable {σ : Type*} {K : Type*} [Field K] {m : MonomialOrder σ}

/-- The `S`-polynomial. -/
noncomputable def sPoly (m : MonomialOrder σ) (f g : MvPolynomial σ K) : MvPolynomial σ K :=
  monomial (m.degree f ⊔ m.degree g - m.degree f) (m.leadingCoeff f)⁻¹ * f -
    monomial (m.degree f ⊔ m.degree g - m.degree g) (m.leadingCoeff g)⁻¹ * g

/-- `S(G i, G j)` is a combination of `G` with all terms below `lcm(deg G i, deg G j)`. -/
def HasLcmRepresentation (m : MonomialOrder σ) {ι : Type*} [Fintype ι]
    (G : ι → MvPolynomial σ K) (i j : ι) : Prop :=
  ∃ H : ι → MvPolynomial σ K, sPoly m (G i) (G j) = ∑ l, H l * G l ∧
    ∀ l, H l * G l = 0 ∨
      m.toSyn (m.degree (H l * G l)) < m.toSyn (m.degree (G i) ⊔ m.degree (G j))

theorem toSyn_degree_monomial_mul_le (s : σ →₀ ℕ) (c : K) (p : MvPolynomial σ K) :
    m.toSyn (m.degree (monomial s c * p)) ≤ m.toSyn s + m.toSyn (m.degree p) := by
  have h1 := m.degree_mul_le (f := monomial s c) (g := p)
  have h2 := m.degree_monomial_le (d := s) c
  rw [← map_add]
  exact h1.trans (by rw [map_add, map_add]; exact add_le_add_left h2 _)

/-- **Representations below the `lcm` give a Gröbner basis.** -/
theorem isGroebnerBasis_of_lcmRepresentation {ι : Type*} [Fintype ι]
    {G : ι → MvPolynomial σ K} (hG0 : ∀ i, G i ≠ 0) (hS : ∀ i j, HasLcmRepresentation m G i j) :
    IsGroebnerBasis m G (Ideal.span (Set.range G)) := by
  classical
  refine ⟨fun i => Ideal.subset_span ⟨i, rfl⟩, fun f hf hf0 => ?_⟩
  -- the largest degree of a representation
  let δ : (ι → MvPolynomial σ K) → m.syn := fun h =>
    Finset.univ.sup fun k => m.toSyn (m.degree (h k * G k))
  set Rset : Set m.syn := {d | ∃ h : ι → MvPolynomial σ K, f = ∑ k, h k * G k ∧ δ h = d}
    with hRset
  have hne : Rset.Nonempty := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
    exact ⟨_, c, hc.symm, rfl⟩
  have hwf : WellFounded (· < · : m.syn → m.syn → Prop) := wellFounded_lt
  obtain ⟨h, hfh, hδ⟩ := hwf.min_mem Rset hne
  have hmin : ∀ h' : ι → MvPolynomial σ K, f = ∑ k, h' k * G k → ¬ δ h' < δ h := by
    intro h' hh'
    rw [hδ]
    exact hwf.not_lt_min Rset ⟨h', hh', rfl⟩
  have hdegf : m.toSyn (m.degree f) ≤ δ h := by
    rw [hfh]; exact m.degree_sum_le
  -- main claim: the minimal `δ` is the degree of `f`
  have hmain : δ h ≤ m.toSyn (m.degree f) := by
    by_contra hlt
    push Not at hlt
    set D := δ h with hD
    have hD0 : 0 < D := lt_of_le_of_lt (m.zero_le _) hlt
    set δm : σ →₀ ℕ := m.toSyn.symm D with hδm
    have hδmD : m.toSyn δm = D := by simp [hδm]
    -- the top indices
    set P := Finset.univ.filter fun k => m.toSyn (m.degree (h k * G k)) = D with hP
    have hle : ∀ k, m.toSyn (m.degree (h k * G k)) ≤ D := fun k =>
      Finset.le_sup (f := fun k => m.toSyn (m.degree (h k * G k))) (Finset.mem_univ k)
    have hP_ne : ∀ k ∈ P, h k ≠ 0 := by
      intro k hk h0
      have := (Finset.mem_filter.mp hk).2
      rw [h0, zero_mul, m.degree_zero, map_zero] at this
      exact (ne_of_lt hD0) this
    have hP_deg : ∀ k ∈ P, m.degree (h k) + m.degree (G k) = δm := by
      intro k hk
      have := (Finset.mem_filter.mp hk).2
      rw [m.degree_mul (hP_ne k hk) (hG0 k)] at this
      exact m.toSyn.injective (this.trans hδmD.symm)
    -- decomposition
    let LT : ι → MvPolynomial σ K := fun k => m.leadingTerm (h k)
    let rest : ι → MvPolynomial σ K := fun k => h k - LT k
    set Q := ∑ k ∈ P, LT k * G k with hQ
    set B := ∑ k ∈ P, rest k * G k + ∑ k ∈ Finset.univ.filter (fun k => k ∉ P), h k * G k
      with hB
    have hfQB : f = Q + B := by
      rw [hfh, hQ, hB, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ P)]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [rest, LT]; ring
    -- every term of `B` is below `D`
    have hrest : ∀ k ∈ P, m.toSyn (m.degree (rest k * G k)) < D := by
      intro k hk
      by_cases hd0 : m.degree (h k) = 0
      · have e1 := m.degree_eq_zero_iff.mp hd0
        have : rest k = 0 := by
          show h k - monomial (m.degree (h k)) (m.leadingCoeff (h k)) = 0
          rw [hd0, ← C_apply]
          exact sub_eq_zero.mpr e1
        rw [this, zero_mul, m.degree_zero, map_zero]; exact hD0
      · have hlt' := m.degree_sub_leadingTerm_lt_degree hd0
        calc m.toSyn (m.degree (rest k * G k))
            ≤ m.toSyn (m.degree (rest k)) + m.toSyn (m.degree (G k)) := by
              rw [← map_add]; exact m.degree_mul_le
          _ < m.toSyn (m.degree (h k)) + m.toSyn (m.degree (G k)) :=
              add_lt_add_left hlt' _
          _ = D := by rw [← map_add, hP_deg k hk, hδmD]
    have hnotP : ∀ k, k ∉ P → m.toSyn (m.degree (h k * G k)) < D := by
      intro k hk
      refine lt_of_le_of_ne (hle k) ?_
      intro heq; exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, heq⟩)
    have hsum_lt : ∀ (s : Finset ι) (F : ι → MvPolynomial σ K),
        (∀ k ∈ s, m.toSyn (m.degree (F k)) < D) → m.toSyn (m.degree (∑ k ∈ s, F k)) < D := by
      intro s F hF
      exact lt_of_le_of_lt m.degree_sum_le ((Finset.sup_lt_iff hD0).mpr hF)
    have hBlt : m.toSyn (m.degree B) < D := by
      refine lt_of_le_of_lt m.degree_add_le (max_lt (hsum_lt _ _ hrest) (hsum_lt _ _ ?_))
      intro k hk; exact hnotP k (Finset.mem_filter.mp hk).2
    have hQlt : m.toSyn (m.degree Q) < D := by
      have : Q = f - B := by rw [hfQB]; ring
      rw [this]
      exact lt_of_le_of_lt m.degree_sub_le (max_lt hlt hBlt)
    -- cancellation of the leading coefficients
    have hcoeffQ : Q.coeff δm = 0 := m.coeff_eq_zero_of_lt (by rw [hδmD]; exact hQlt)
    have hcoeffk : ∀ k ∈ P, (LT k * G k).coeff δm =
        m.leadingCoeff (h k) * m.leadingCoeff (G k) := by
      intro k hk
      show (monomial (m.degree (h k)) (m.leadingCoeff (h k)) * G k).coeff δm = _
      rw [← hP_deg k hk, coeff_monomial_mul]
      rfl
    have hsum0 : ∑ k ∈ P, m.leadingCoeff (h k) * m.leadingCoeff (G k) = 0 := by
      rw [← hcoeffQ, hQ, coeff_sum]
      exact Finset.sum_congr rfl fun k hk => (hcoeffk k hk).symm
    -- a top index
    obtain ⟨k₀, hk₀P⟩ : ∃ k₀, k₀ ∈ P := by
      have huniv : (Finset.univ : Finset ι).Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        apply hf0; rw [hfh, he, Finset.sum_empty]
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup _ huniv
        (fun k => m.toSyn (m.degree (h k * G k)))
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk.symm⟩⟩
    -- the normalized top terms
    let q : ι → MvPolynomial σ K := fun k =>
      monomial (m.degree (h k)) (m.leadingCoeff (G k))⁻¹ * G k
    let a : ι → K := fun k => m.leadingCoeff (h k) * m.leadingCoeff (G k)
    have hLTq : ∀ k, LT k * G k = C (a k) * q k := by
      intro k
      have hlc : m.leadingCoeff (G k) ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr (hG0 k)
      simp only [LT, leadingTerm, q, a, ← mul_assoc, C_mul_monomial]
      congr 2
      field_simp
    have hQstar : Q = ∑ k ∈ P, C (a k) * (q k - q k₀) := by
      have : ∑ k ∈ P, C (a k) * q k₀ = 0 := by
        rw [← Finset.sum_mul, ← map_sum, hsum0, map_zero, zero_mul]
      rw [hQ, Finset.sum_congr rfl fun k _ => hLTq k]
      simp only [mul_sub, Finset.sum_sub_distrib, this, sub_zero]
    -- `q k − q k₀` through the `S`-polynomial
    have hqS : ∀ k ∈ P, q k - q k₀ =
        monomial (δm - (m.degree (G k) ⊔ m.degree (G k₀))) 1 * sPoly m (G k) (G k₀) := by
      intro k hk
      have hk1 : m.degree (G k) ≤ δm := by rw [← hP_deg k hk]; exact le_add_self
      have hk2 : m.degree (G k₀) ≤ δm := by rw [← hP_deg k₀ hk₀P]; exact le_add_self
      have hγ : m.degree (G k) ⊔ m.degree (G k₀) ≤ δm := sup_le hk1 hk2
      have e1 : δm - m.degree (G k) = m.degree (h k) := by
        rw [← hP_deg k hk, add_tsub_cancel_right]
      have e2 : δm - m.degree (G k₀) = m.degree (h k₀) := by
        rw [← hP_deg k₀ hk₀P, add_tsub_cancel_right]
      simp only [sPoly, q, mul_sub, ← mul_assoc, monomial_mul_monomial, one_mul]
      rw [tsub_add_tsub_cancel hγ le_sup_left, tsub_add_tsub_cancel hγ le_sup_right, e1, e2]
    -- representations of the `S`-polynomials
    choose H hHsum hHdeg using fun k => hS k k₀
    let M : ι → MvPolynomial σ K := fun k =>
      monomial (δm - (m.degree (G k) ⊔ m.degree (G k₀))) 1
    let H' : ι → MvPolynomial σ K := fun l => ∑ k ∈ P, C (a k) * (M k * H k l)
    have hQH : Q = ∑ l, H' l * G l := by
      rw [hQstar, Finset.sum_congr rfl fun k hk => by rw [hqS k hk, hHsum k]]
      simp only [H', Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hH'lt : ∀ l, m.toSyn (m.degree (H' l * G l)) < D := by
      intro l
      have : H' l * G l = ∑ k ∈ P, C (a k) * (M k * (H k l * G l)) := by
        simp only [H', Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]
      refine hsum_lt _ _ fun k hk => ?_
      have hk1 : m.degree (G k) ≤ δm := by rw [← hP_deg k hk]; exact le_add_self
      have hk2 : m.degree (G k₀) ≤ δm := by rw [← hP_deg k₀ hk₀P]; exact le_add_self
      have hγ : m.degree (G k) ⊔ m.degree (G k₀) ≤ δm := sup_le hk1 hk2
      have hC : m.toSyn (m.degree (C (a k) * (M k * (H k l * G l)))) ≤
          m.toSyn (m.degree (M k * (H k l * G l))) := by
        rw [← smul_eq_C_mul]; exact m.degree_smul_le
      refine lt_of_le_of_lt hC ?_
      rcases hHdeg k l with h0 | hlt'
      · rw [h0, mul_zero, m.degree_zero, map_zero]; exact hD0
      · calc m.toSyn (m.degree (M k * (H k l * G l)))
            ≤ m.toSyn (δm - (m.degree (G k) ⊔ m.degree (G k₀))) +
                m.toSyn (m.degree (H k l * G l)) := toSyn_degree_monomial_mul_le _ _ _
          _ < m.toSyn (δm - (m.degree (G k) ⊔ m.degree (G k₀))) +
                m.toSyn (m.degree (G k) ⊔ m.degree (G k₀)) := (add_lt_add_iff_left _).mpr hlt'
          _ = D := by rw [← map_add, tsub_add_cancel_of_le hγ, hδmD]
    -- the new representation
    let h' : ι → MvPolynomial σ K := fun l => H' l + if l ∈ P then rest l else h l
    have hfh' : f = ∑ l, h' l * G l := by
      rw [hfQB, hQH, hB]
      simp only [h', add_mul, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ P)]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      congr 1
      · exact Finset.sum_congr rfl fun k hk => by simp only [hk, ↓reduceIte]
      · exact Finset.sum_congr rfl fun k hk => by
          simp only [(Finset.mem_filter.mp hk).2, ↓reduceIte]
    have hδ' : δ h' < D := by
      refine (Finset.sup_lt_iff hD0).mpr fun l _ => ?_
      simp only [h', add_mul]
      refine lt_of_le_of_lt m.degree_add_le (max_lt (hH'lt l) ?_)
      by_cases hl : l ∈ P
      · simp only [hl, ↓reduceIte]; exact hrest l hl
      · simp only [hl, ↓reduceIte]; exact hnotP l hl
    exact hmin h' hfh' hδ'
  -- conclude: some term has the degree of `f`
  by_contra hno
  push Not at hno
  have hcf : f.coeff (m.degree f) ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf0
  apply hcf
  have hco : f.coeff (m.degree f) = (∑ k, h k * G k).coeff (m.degree f) := by rw [← hfh]
  rw [hco, coeff_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : h k = 0
  · simp [hk]
  · refine m.coeff_eq_zero_of_lt (lt_of_le_of_ne ?_ ?_)
    · exact (Finset.le_sup (f := fun k => m.toSyn (m.degree (h k * G k)))
        (Finset.mem_univ k)).trans hmain
    · intro heq
      apply hno k
      have hdeq : m.degree (h k * G k) = m.degree f := m.toSyn.injective heq
      rw [m.degree_mul hk (hG0 k)] at hdeq
      rw [← hdeq]; exact le_add_self

/-- Each half of the `S`-polynomial has degree `γ = lcm` and leading coefficient `1`. -/
theorem sPoly_half_degree_le {f : MvPolynomial σ K} {γ : σ →₀ ℕ} (hγ : m.degree f ≤ γ) :
    m.toSyn (m.degree (monomial (γ - m.degree f) (m.leadingCoeff f)⁻¹ * f)) ≤ m.toSyn γ := by
  refine (toSyn_degree_monomial_mul_le _ _ _).trans (le_of_eq ?_)
  rw [← map_add, tsub_add_cancel_of_le hγ]

theorem sPoly_half_coeff {f : MvPolynomial σ K} (hf : f ≠ 0) {γ : σ →₀ ℕ} (hγ : m.degree f ≤ γ) :
    (monomial (γ - m.degree f) (m.leadingCoeff f)⁻¹ * f).coeff γ = 1 := by
  have e := coeff_monomial_mul (m.degree f) (γ - m.degree f) (m.leadingCoeff f)⁻¹ f
  rw [tsub_add_cancel_of_le hγ] at e
  rw [e]
  exact inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.mpr hf)

/-- **The `S`-polynomial lies below the `lcm`.** -/
theorem sPoly_degree_lt {f g : MvPolynomial σ K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hS : sPoly m f g ≠ 0) :
    m.toSyn (m.degree (sPoly m f g)) < m.toSyn (m.degree f ⊔ m.degree g) := by
  have hle : m.toSyn (m.degree (sPoly m f g)) ≤ m.toSyn (m.degree f ⊔ m.degree g) :=
    m.degree_sub_le.trans (max_le (sPoly_half_degree_le le_sup_left)
      (sPoly_half_degree_le le_sup_right))
  refine lt_of_le_of_ne hle fun heq => ?_
  have hdeq : m.degree (sPoly m f g) = m.degree f ⊔ m.degree g := m.toSyn.injective heq
  have hc : (sPoly m f g).coeff (m.degree f ⊔ m.degree g) = 0 := by
    simp only [sPoly, coeff_sub, sPoly_half_coeff hf le_sup_left,
      sPoly_half_coeff hg le_sup_right, sub_self]
  have hmem := (m.degree_mem_support_iff (sPoly m f g)).mpr hS
  rw [hdeq, mem_support_iff] at hmem
  exact hmem hc

/-- `S(G i, G j)` **reduces to zero**: it is a combination of `G` with every term of degree at most
the degree of the `S`-polynomial (the output of the division algorithm with zero remainder). -/
def SPolyReducesToZero (m : MonomialOrder σ) {ι : Type*} [Fintype ι]
    (G : ι → MvPolynomial σ K) (i j : ι) : Prop :=
  ∃ g : ι → MvPolynomial σ K, sPoly m (G i) (G j) = ∑ l, g l * G l ∧
    ∀ l, m.toSyn (m.degree (G l * g l)) ≤ m.toSyn (m.degree (sPoly m (G i) (G j)))

theorem hasLcmRepresentation_of_reducesToZero {ι : Type*} [Fintype ι]
    {G : ι → MvPolynomial σ K} (hG0 : ∀ i, G i ≠ 0) {i j : ι}
    (h : SPolyReducesToZero m G i j) : HasLcmRepresentation m G i j := by
  by_cases hS : sPoly m (G i) (G j) = 0
  · exact ⟨0, by simp [hS], fun l => Or.inl (by simp)⟩
  obtain ⟨g, hsum, hdeg⟩ := h
  refine ⟨g, hsum, fun l => Or.inr ?_⟩
  rw [mul_comm]
  exact lt_of_le_of_lt (hdeg l) (sPoly_degree_lt (hG0 i) (hG0 j) hS)

/-- **Buchberger's criterion.** A finite family `G` of nonzero polynomials over a field is a
Gröbner basis of the ideal it generates iff, for all `i, j`, dividing `S(G i, G j)` by `G` (in the
sense of `MonomialOrder.div`) leaves remainder zero. -/
theorem isGroebnerBasis_iff_remainders_zero {ι : Type*} [Fintype ι]
    {G : ι → MvPolynomial σ K} (hG0 : ∀ i, G i ≠ 0) :
    IsGroebnerBasis m G (Ideal.span (Set.range G)) ↔
      ∀ i j (g : ι →₀ MvPolynomial σ K) (r : MvPolynomial σ K),
        sPoly m (G i) (G j) = Finsupp.linearCombination (MvPolynomial σ K) G g + r →
        (∀ c ∈ r.support, ∀ l, ¬ m.degree (G l) ≤ c) → r = 0 := by
  classical
  constructor
  · intro hGB i j g r hdiv hr
    have hmem : sPoly m (G i) (G j) ∈ Ideal.span (Set.range G) := by
      unfold sPoly
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))
    exact (hGB.mem_iff_remainder_eq_zero hdiv hr).mp hmem
  · intro h
    refine isGroebnerBasis_of_lcmRepresentation hG0 fun i j => ?_
    have hb : ∀ l, IsUnit (m.leadingCoeff (G l)) := fun l =>
      isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr (hG0 l))
    obtain ⟨g, r, hdiv, hdeg, hr⟩ := m.div hb (sPoly m (G i) (G j))
    have hr0 := h i j g r hdiv hr
    refine hasLcmRepresentation_of_reducesToZero hG0 ⟨fun l => g l, ?_, hdeg⟩
    rw [hdiv, hr0, add_zero, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul]
    · intro l; simp

/-- **Buchberger's criterion, representation form.** If every `S(G i, G j)` reduces to zero, `G` is
a Gröbner basis of the ideal it generates. -/
theorem isGroebnerBasis_of_reducesToZero {ι : Type*} [Fintype ι] {G : ι → MvPolynomial σ K}
    (hG0 : ∀ i, G i ≠ 0) (h : ∀ i j, SPolyReducesToZero m G i j) :
    IsGroebnerBasis m G (Ideal.span (Set.range G)) :=
  isGroebnerBasis_of_lcmRepresentation hG0 fun i j =>
    hasLcmRepresentation_of_reducesToZero hG0 (h i j)

end Groebner

end CRNT
