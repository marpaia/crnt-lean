import CRNT.Stochastic.EndotacticTierDomination

/-!
# Restricted stochastic count-lattice criteria and the one-species case

Structural consequences of strong endotacticity, falling-factorial comparison
obstructions, and the one-species drift argument. Count-tier matching assumptions
are extra hypotheses for the several-species transfer. Recurrence statements
retain their irreducibility assumptions.

There is no universal several-species strong-endotactic recurrence/non-explosion
theorem: the unrestricted assertion is false (Anderson–Cappelletti–Kim–Nguyen,
arXiv:1808.05328, Examples 3.1–3.2). This module's name is historical and does not
indicate completion of that false general assertion.
-/

open Filter Topology
open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. The deterministic hypothesis, read off precisely -/

omit [DecidableEq S] in
/-- **The complex potential of a complex.**  The `w`-potential of a complex `y` is the weighted
sum of its molecularities. -/
theorem complexWValue_eq (w : S → ℝ) (y : Complex S) :
    complexWValue w y = ∑ s, w s * ((y s : ℕ) : ℝ) := by
  unfold complexWValue dotProduct exponentVector
  rfl

/-- **The `w`-rate of a reaction in a direction that singles out one species.**  In the direction
`w = (if t = s then w s else 0)` the `w`-rate of a reaction is the change of the `s`-content of
the reaction. -/
theorem wRate_eq_indicator {N : Network S} (w : S → ℝ) (r : N.R) (s : S) :
    N.wRate (fun t => if t = s then w s else 0) r =
      w s * (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) := by
  rw [N.wRate_eq]
  have hstep : (∑ t : S, (if t = s then w s else 0) *
        (((N.reaction r).target t : ℝ) - ((N.reaction r).source t : ℝ))) =
      (∑ t : S, if t = s then w s *
        (((N.reaction r).target t : ℝ) - ((N.reaction r).source t : ℝ)) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : t = s <;> simp [h]
  rw [hstep, Finset.sum_ite_eq' _ s]
  simp

/-- **The `w`-rate of a reaction in the direction that counts one species.** -/
theorem wRate_eq_species {N : Network S} (r : N.R) (s : S) :
    N.wRate (fun t => if t = s then (1 : ℝ) else 0) r =
      ((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ) := by
  rw [N.wRate_eq]
  have hstep : (∑ t : S, (if t = s then (1 : ℝ) else 0) *
        (((N.reaction r).target t : ℝ) - ((N.reaction r).source t : ℝ))) =
      (∑ t : S, if t = s then
        (((N.reaction r).target t : ℝ) - ((N.reaction r).source t : ℝ)) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : t = s <;> simp [h]
  rw [hstep, Finset.sum_ite_eq' _ s]
  simp

/-- **The `w`-value of a reaction in a direction that singles out one species.** -/
theorem wValue_eq_indicator {N : Network S} (w : S → ℝ) (r : N.R) (s : S) :
    N.wValue (fun t => if t = s then w s else 0) r =
      w s * ((N.reaction r).source s : ℝ) := by
  rw [N.wValue_eq_complexWValue_source, complexWValue_eq]
  have hstep : (∑ t : S, (if t = s then w s else 0) * (((N.reaction r).source t : ℕ) : ℝ))
      = (∑ t : S, if t = s then w s * (((N.reaction r).source t : ℕ) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : t = s <;> simp [h]
  rw [hstep, Finset.sum_ite_eq' _ s]
  simp

/-- **The `w`-value of a reaction in the direction that counts one species.** -/
theorem wValue_eq_species {N : Network S} (r : N.R) (s : S) :
    N.wValue (fun t => if t = s then (1 : ℝ) else 0) r =
      ((N.reaction r).source s : ℝ) := by
  rw [N.wValue_eq_complexWValue_source, complexWValue_eq]
  have hstep : (∑ t : S, (if t = s then (1 : ℝ) else 0) * (((N.reaction r).source t : ℕ) : ℝ))
      = (∑ t : S, if t = s then (((N.reaction r).source t : ℕ) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : t = s <;> simp [h]
  rw [hstep, Finset.sum_ite_eq' _ s]
  simp

/-- **Endotacticity at a maximal source.**  If the source complex of `r` maximises the `w`-value
among the source complexes, then the reaction does not ascend the tier potential.  This is the
first half of `CRNT.Network.StronglyEndotacticStd`, isolated. -/
theorem StronglyEndotacticStd.le_of_maxSource {N : Network S} (h : N.StronglyEndotacticStd)
    (w : S → ℝ) (r : N.R) (hmax : N.IsMaxSource w r) : N.wRate w r ≤ 0 :=
  h.1 w r hmax

/-- **The strict descent at the top tier.**  For every stoichiometrically active direction there
is a `w`-maximal reaction that descends the tier potential strictly.  This is the second half of
`CRNT.Network.StronglyEndotacticStd`, isolated. -/
theorem StronglyEndotacticStd.exists_maxSource_descending {N : Network S}
    (h : N.StronglyEndotacticStd) {w : S → ℝ} (hw : N.StoichActiveDirection w) :
    ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0 :=
  h.2 w hw

/-- **A maximal source does not produce the species that is maximal there.**  If the source of
`r` maximises the `s`-content among the source complexes of the network, then `r` does not
produce `s`: the `s`-content of `r` cannot increase at the maximal face of the `s`-content.

This is the reaction-wise form of the deterministic hypothesis that the count-lattice transfer
uses: it says that *every* reaction that produces a species sits strictly below the maximal
content of that species. -/
theorem StronglyEndotacticStd.target_le_source_of_maxSource {N : Network S}
    (h : N.StronglyEndotacticStd) (r : N.R) (s : S)
    (hmax : N.IsMaxSource (fun t => if t = s then (1 : ℝ) else 0) r) :
    (N.reaction r).target s ≤ (N.reaction r).source s := by
  have h1 := h.le_of_maxSource (fun t => if t = s then (1 : ℝ) else 0) r hmax
  rw [wRate_eq_species] at h1
  have h2 : ((N.reaction r).target s : ℝ) ≤ ((N.reaction r).source s : ℝ) := by
    linarith
  exact_mod_cast h2

/-- **A reaction that produces a species cannot sit at the maximal content of that species.** -/
theorem StronglyEndotacticStd.not_maxSource_of_produced {N : Network S}
    (h : N.StronglyEndotacticStd) (r : N.R) (s : S)
    (hprod : (N.reaction r).target s > (N.reaction r).source s) :
    ¬ N.IsMaxSource (fun t => if t = s then (1 : ℝ) else 0) r := by
  intro hmax
  have h1 := h.target_le_source_of_maxSource r s hmax
  linarith

/-- **A reaction that produces a species has a competitor with more of that species.**  There is
a reaction of the network whose source contains strictly more molecules of `s` than the source
of `r`.

Together with `StronglyEndotacticStd.not_maxSource_of_produced` this says: the *deterministic*
hypothesis already forbids a reaction from being the last word about the species it produces.
What it does **not** say is that the competing reaction descends the tier potential, or that it
has the same source complex: that is exactly the gap that §2 and §3 below make precise. -/
theorem StronglyEndotacticStd.exists_source_more_of_species {N : Network S}
    (h : N.StronglyEndotacticStd) (r : N.R) (s : S)
    (hprod : (N.reaction r).target s > (N.reaction r).source s) :
    ∃ r' : N.R, (N.reaction r').source s > (N.reaction r).source s := by
  by_contra hcon
  refine h.not_maxSource_of_produced r s hprod ?_
  intro r'
  rw [wValue_eq_species, wValue_eq_species]
  by_contra hnotle
  have hgt : (N.reaction r').source s > (N.reaction r).source s := by
    have h1 : ¬ ((N.reaction r').source s : ℝ) ≤ ((N.reaction r).source s : ℝ) := hnotle
    have h2 : ((N.reaction r).source s : ℝ) < ((N.reaction r').source s : ℝ) :=
      lt_of_not_ge h1
    exact_mod_cast h2
  exact hcon ⟨r', hgt⟩

/-! ## 2. The sharp count-lattice comparison -/

omit [DecidableEq S] in
/-- The count-lattice falling factorial of an **enabled** complex is strictly positive. -/
theorem countDescFactorial_pos_of_enabled {y : Complex S} {n : S → ℕ}
    (h : ∀ s, y s ≤ n s) : 0 < countDescFactorial y n := by
  unfold countDescFactorial
  exact Finset.prod_pos fun s _ => (Nat.descFactorial_pos).2 (h s)

omit [DecidableEq S] in
/-- The count-lattice falling factorial of a complex that is **not enabled** vanishes.  This is
the truncation obstruction of the count lattice. -/
theorem countDescFactorial_eq_zero_of_not_enabled {y : Complex S} {n : S → ℕ}
    (h : ∃ s, y s > n s) : countDescFactorial y n = 0 := by
  obtain ⟨s, hs⟩ := h
  unfold countDescFactorial
  refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
  rw [Nat.descFactorial_eq_zero_iff_lt]
  omega

omit [DecidableEq S] in
/-- The count-lattice falling factorial of an **enabled** complex, as a real number, is strictly
positive. -/
theorem countDescFactorial_pos_of_enabled' {y : Complex S} {n : S → ℕ}
    (h : ∀ s, y s ≤ n s) : 0 < (countDescFactorial y n : ℝ) := by
  have h1 := countDescFactorial_pos_of_enabled h
  exact_mod_cast h1

/-- **The sharp count-lattice tier domination.**  The count-lattice monomial of `y` dominates
that of `z` on the whole region where `z` is enabled **if and only if the two complexes
coincide**.

This is the exact statement of the condition under which the comparison of the field map's route
holds.  In particular, the "top-tier monomial dominates the lower-tier monomials" step is
possible on the count lattice *only* when the top-tier complex and the lower-tier complex are
the same complex; the deterministic theory, which compares the mass-action monomials
`x^y ≫ x^z` for distinct complexes, has no counterpart here.

The proof is by contradiction.  If `y` has more molecules of some species than `z`, the complex
`y` is not enabled at the count `z` and its falling factorial vanishes there, while that of `z`
is strictly positive.  If `y ≤ z` and `y ≠ z`, the falling factorial of `z` eventually exceeds
that of `y` (a polynomial of larger degree), so the domination fails there. -/
theorem countDescFactorial_dominates_iff {y z : Complex S} :
    (∀ n : S → ℕ, (∀ s, z s ≤ n s) → countDescFactorial y n ≥ countDescFactorial z n) ↔ y = z := by
  constructor
  · intro h
    by_contra hne
    by_cases hle : ∀ s, y s ≤ z s
    · -- `y ≤ z` and `y ≠ z`: the ratio `n^{↓z} / n^{↓y}` is unbounded
      have hne' : ∃ s, y s ≠ z s := not_forall.mp (fun h => hne (funext h))
      obtain ⟨s₀, hs₀⟩ := hne'
      have hslt : y s₀ < z s₀ := by
        rcases Nat.lt_or_gt_of_ne hs₀ with h | h
        · exact h
        · exact absurd h (Nat.not_lt_of_ge (hle s₀))
      set n : S → ℕ := fun t => if t = s₀ then z s₀ + 1 else z t with hndef
      have hzn : ∀ t, z t ≤ n t := by
        intro t
        have h1 : n t = if t = s₀ then z s₀ + 1 else z t := by simp [hndef]
        rw [h1]
        split
        · next hcond =>
          have h2 : z t = z s₀ := by rw [hcond]
          rw [h2]
          omega
        · omega
      have hnslack : (n s₀ : ℝ) ≥ 1 + (z s₀ : ℝ) := by
        have h1 : (n s₀ : ℝ) = ((z s₀ + 1 : ℕ) : ℝ) := by simp [hndef]
        rw [h1]
        push_cast
        linarith
      have hratio := countDescFactorial_ratio_gt_of_count (y := z) (z := y) (n := n) (M := 1)
        (by norm_num) hle hzn s₀ hslt hnslack
      have hpos : 0 < (countDescFactorial y n : ℝ) :=
        countDescFactorial_pos_of_enabled' (fun s => le_trans (hle s) (hzn s))
      have h1 : (countDescFactorial y n : ℝ) < (countDescFactorial z n : ℝ) := by
        have h2 : (1 : ℝ) < (countDescFactorial z n : ℝ) / (countDescFactorial y n : ℝ) := by
          linarith [hratio]
        have h3 : (1 : ℝ) * (countDescFactorial y n : ℝ) <
            (countDescFactorial y n : ℝ) *
              ((countDescFactorial z n : ℝ) / (countDescFactorial y n : ℝ)) := by
          simpa using mul_lt_mul_of_pos_left h2 hpos
        have h4 : (countDescFactorial y n : ℝ) *
              ((countDescFactorial z n : ℝ) / (countDescFactorial y n : ℝ)) =
            (countDescFactorial z n : ℝ) := by
          field_simp
        rw [h4] at h3
        linarith
      have h2 := h n hzn
      have h2' : ((countDescFactorial y n : ℕ) : ℝ) ≥ ((countDescFactorial z n : ℕ) : ℝ) := by
        exact_mod_cast h2
      linarith
    · -- `y` has more molecules than `z` somewhere: `y` is not enabled at the count `z`
      have hne' : ∃ s, ¬ (y s ≤ z s) := not_forall.mp hle
      obtain ⟨s₀, hs₀⟩ := hne'
      have hslt : z s₀ < y s₀ := Nat.lt_of_not_ge hs₀
      have h1 : countDescFactorial y z = 0 :=
        countDescFactorial_eq_zero_of_not_enabled ⟨s₀, hslt⟩
      have h2 : 0 < countDescFactorial z z := countDescFactorial_pos_of_enabled (fun s => le_refl _)
      have h3 := h z (fun s => le_refl _)
      linarith
  · intro rfl n _
    exact le_refl _

/-- **No uniform domination by a distinct complex.**  If `y ≠ z` there is no constant `c > 0`
such that the count-lattice monomial of `z` dominates that of `y` by the factor `c` on the whole
region where `y` is enabled.

Combined with `countDescFactorial_dominates_iff` this says that on the count lattice the
comparison of the field map's route is *impossible* between two distinct complexes: the
falling factorial of a complex that is not enabled vanishes, and no distinct complex dominates
`y` by a uniform factor either. -/
theorem countDescFactorial_no_uniform_domination {y z : Complex S} (hne : y ≠ z) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : S → ℕ, (∀ s, y s ≤ n s) →
      (countDescFactorial z n : ℝ) ≥ c * (countDescFactorial y n : ℝ) := by
  rintro ⟨c, hc, h⟩
  by_cases hzy : ∀ s, z s ≤ y s
  · -- `z ≤ y` and `z ≠ y`: the ratio `n^{↓y} / n^{↓z}` is unbounded
    have hne' : ∃ s, z s ≠ y s := not_forall.mp (fun hh => hne (funext fun s => (hh s).symm))
    obtain ⟨s₀, hs₀⟩ := hne'
    have hslt : z s₀ < y s₀ := by
      rcases Nat.lt_or_gt_of_ne hs₀ with hh | hh
      · exact hh
      · exact absurd hh (Nat.not_lt_of_ge (hzy s₀))
    -- the threshold `M` and the count `K` above it
    have hcinv : (0 : ℝ) < 1 / c := by positivity
    have hMpos : (0 : ℝ) < 1 / c + 1 := by linarith
    have hMbig : (1 / c : ℝ) < 1 / c + 1 := by linarith
    set K : ℕ := Nat.ceil (1 / c + 1) + 1 with hKdef
    have hKbig : (1 / c + 1 : ℝ) ≤ (K : ℝ) := by
      have h1 : (1 / c + 1 : ℝ) ≤ (Nat.ceil (1 / c + 1) : ℝ) := Nat.le_ceil _
      have h2 : (K : ℝ) = (Nat.ceil (1 / c + 1) : ℝ) + 1 := by simp [hKdef]
      linarith
    set n : S → ℕ := fun t => if t = s₀ then y s₀ + K else y t with hndef
    have hn0 : n s₀ = y s₀ + K := by simp [hndef]
    have hnle : ∀ t, y t ≤ n t := by
      intro t
      by_cases ht : t = s₀
      · have h1 : n t = y s₀ + K := by simp [hndef, ht]
        rw [h1]
        have h2 : y t = y s₀ := by rw [ht]
        rw [h2]
        omega
      · have h1 : n t = y t := by simp [hndef, ht]
        rw [h1]
    have hnslack : (n s₀ : ℝ) ≥ (1 / c + 1 : ℝ) + (y s₀ : ℝ) := by
      rw [hn0]
      push_cast
      linarith [hKbig]
    have hratio := countDescFactorial_ratio_gt_of_count (y := y) (z := z) (n := n)
      (M := 1 / c + 1) hMpos hzy hnle s₀ hslt hnslack
    have hzpos : 0 < (countDescFactorial z n : ℝ) :=
      countDescFactorial_pos_of_enabled' (fun s => le_trans (hzy s) (hnle s))
    have hstep : (countDescFactorial z n : ℝ) * (1 / c + 1) < (countDescFactorial y n : ℝ) := by
      have h1 : (1 / c + 1 : ℝ) < (countDescFactorial y n : ℝ) / (countDescFactorial z n : ℝ) :=
        hratio
      have h2 := (lt_div_iff₀' hzpos).mp h1
      simpa [mul_comm] using h2
    have hdiv : (countDescFactorial z n : ℝ) < (countDescFactorial y n : ℝ) / (1 / c + 1) := by
      have h1 : (1 / c + 1 : ℝ) * (countDescFactorial z n : ℝ) < (countDescFactorial y n : ℝ) := by
        simpa [mul_comm] using hstep
      have h2 := (lt_div_iff₀' hMpos).mpr h1
      exact h2
    have hrecip : (1 / (1 / c + 1) : ℝ) < c := by
      have h1 := one_div_lt_one_div_of_lt hcinv hMbig
      have h2 : (1 / (1 / c) : ℝ) = c := by field_simp
      rw [h2] at h1
      exact h1
    have hypos : 0 ≤ (countDescFactorial y n : ℝ) :=
      (countDescFactorial_pos_of_enabled' hnle).le
    have h3 : (countDescFactorial y n : ℝ) / (1 / c + 1) ≤ c * (countDescFactorial y n : ℝ) := by
      rw [div_eq_mul_inv]
      have h1 : (countDescFactorial y n : ℝ) * (1 / (1 / c + 1) : ℝ) ≤
          (countDescFactorial y n : ℝ) * c :=
        mul_le_mul_of_nonneg_left hrecip.le hypos
      simpa [mul_comm] using h1
    have h2 : (countDescFactorial z n : ℝ) < c * (countDescFactorial y n : ℝ) := by
      linarith
    have h1 := h n hnle
    linarith
  · -- `z` has more molecules than `y` somewhere: `z` is not enabled at the count `y`
    have hne' : ∃ s, ¬ (z s ≤ y s) := not_forall.mp hzy
    obtain ⟨s₀, hs₀⟩ := hne'
    have hslt : y s₀ < z s₀ := Nat.lt_of_not_ge hs₀
    have h1 : countDescFactorial z y = 0 :=
      countDescFactorial_eq_zero_of_not_enabled ⟨s₀, hslt⟩
    have h2 : 0 < countDescFactorial y y := countDescFactorial_pos_of_enabled (fun s => le_refl _)
    have h2' : (0 : ℝ) < (countDescFactorial y y : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < c * (countDescFactorial y y : ℝ) := mul_pos hc h2'
    have h3 := h y (fun s => le_refl _)
    simp only [h1] at h3
    have h5 : (0 : ℝ) ≥ c * (countDescFactorial y y : ℝ) := by simpa using h3
    linarith

/-! ## 3. The count-lattice matching is forced -/

/-- **The descending partner of an ascending reaction must have the same source complex.**
Suppose the ascending reaction `r` (with source complex `y`) is cancelled, on the whole region
where `r` is enabled, by a descending reaction `r'` (with source complex `z`) — that is, there
is a constant `c > 0` such that the count-lattice monomial of `z` dominates that of `y` by the
factor `c` at every count at which `r` is enabled.  Then `z = y`.

This is the precise reason why the "balance" hypothesis of `CRNT.Network.CountTierBalance` is
not a modelling choice: on the count lattice it is the *only* way a single descending reaction
can cancel an ascending one on the whole enabled region. -/
theorem partner_same_source {N : Network S} {r r' : N.R}
    {c : ℝ} (hc : 0 < c)
    (h : ∀ n : S → ℕ, (∀ s, (N.reaction r).source s ≤ n s) →
      (countDescFactorial (N.reaction r').source n : ℝ) ≥
        c * (countDescFactorial (N.reaction r).source n : ℝ)) :
    (N.reaction r').source = (N.reaction r).source := by
  by_contra hne
  exact countDescFactorial_no_uniform_domination
    (y := (N.reaction r).source) (z := (N.reaction r').source) (Ne.symm hne) ⟨c, hc, h⟩

/-- **The balance hypothesis is forced.**  In a balanced count-lattice tier structure the partner
of an ascending reaction has the *same* source complex as the ascending reaction; this is a
consequence of the structure, and `partner_same_source` shows that no other choice is possible
on the count lattice. -/
theorem CountTierBalance.partner_same_source {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) (r : N.R)
    (hasc : N.wRate B.w r > 0) (hne : ComplexNonempty (N.reaction r).source) :
    (N.reaction (B.partner r)).source = (N.reaction r).source :=
  (B.hpartner r hasc hne).2.1

/-! ## 4. The Anderson--Cappelletti--Kim--Nguyen theorem for one species -/

namespace OneSpecies

open Network

variable {R : Type} [DecidableEq R] [Fintype R]

/-- The molecularity of the source complex of a reaction in a one-species network. -/
def srcMol (N : Network (Fin 1)) (r : N.R) : ℕ := (N.reaction r).source 0

/-- The molecularity of the target complex of a reaction in a one-species network. -/
def tgtMol (N : Network (Fin 1)) (r : N.R) : ℕ := (N.reaction r).target 0

/-- The tier drop of a reaction in a one-species network: the change of the total count. -/
def tierDrop (N : Network (Fin 1)) (r : N.R) : ℝ :=
  ((N.reaction r).target 0 : ℝ) - ((N.reaction r).source 0 : ℝ)

/-- **The tier potential of a one-species reaction** in the total-count direction `w = 1` is the
molecularity of its source complex. -/
theorem wValue_total (N : Network (Fin 1)) (r : N.R) :
    N.wValue (fun _ => (1 : ℝ)) r = (srcMol N r : ℝ) := by
  rw [N.wValue_eq_complexWValue_source, complexWValue_eq]
  simp [srcMol]

/-- **The tier rate of a one-species reaction** in the total-count direction `w = 1` is the
change of the total count. -/
theorem wRate_total (N : Network (Fin 1)) (r : N.R) :
    N.wRate (fun _ => (1 : ℝ)) r = tierDrop N r := by
  rw [N.wRate_eq]
  simp [tierDrop]

/-- **The count-lattice falling factorial of the source complex of a one-species reaction**
depends only on the count of the single species. -/
theorem countDescFactorial_src (N : Network (Fin 1)) (r : N.R) (n : Fin 1 → ℕ) :
    countDescFactorial (N.reaction r).source n = (n 0).descFactorial (srcMol N r) := by
  unfold countDescFactorial srcMol
  simp

/-- **The maximal sources of the total-count direction** are the reactions of maximal
molecularity. -/
theorem isMaxSource_iff (N : Network (Fin 1)) (r : N.R) :
    N.IsMaxSource (fun _ => (1 : ℝ)) r ↔ ∀ r' : N.R, srcMol N r' ≤ srcMol N r := by
  constructor
  · intro h r'
    have h1 := h r'
    rw [wValue_total, wValue_total] at h1
    exact_mod_cast h1
  · intro h r'
    have h1 := h r'
    rw [wValue_total, wValue_total]
    exact_mod_cast h1

/-- **The drift of the total count of a one-species network.** -/
theorem observableGenerator_total (N : Network (Fin 1)) (κ : N.RateConstants)
    (n : Fin 1 → ℕ) :
    N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n =
      ∑ r : N.R, (κ.k r) * ((countDescFactorial (N.reaction r).source n : ℝ)) * tierDrop N r := by
  rw [N.observableGenerator_linear]
  apply Finset.sum_congr rfl
  intro r _
  have h : (∑ s : Fin 1, (1 : ℝ) * N.reactionVector r s) =
      (1 : ℝ) * (((N.reaction r).target 0 : ℝ) - ((N.reaction r).source 0 : ℝ)) := by
    simp [Network.reactionVector_apply]
  rw [h, stochasticMassActionRate_eq_countDescFactorial N κ n r]
  simp only [tierDrop]
  ring

/-- The total count of a count vector of a one-species network. -/
theorem linearObservable_total (n : Fin 1 → ℕ) :
    linearObservable (fun _ => (1 : ℝ)) n = (n 0 : ℝ) := by
  simp [linearObservable]

/-- If all the terms of a sum are nonpositive, the sum over a superset is at most the sum over a
subset: the omitted terms are nonpositive. -/
private theorem sum_le_sum_of_subset_of_nonpos {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (A B : Finset ι) (hBA : B ⊆ A) (hf : ∀ i ∈ A, f i ≤ 0) :
    ∑ i ∈ A, f i ≤ ∑ i ∈ B, f i := by
  classical
  have hfilter : A.filter (fun i => i ∈ B) = B := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hBA h, h⟩
  have hsplit : (∑ i ∈ A, f i) = (∑ i ∈ A.filter (fun i => i ∈ B), f i) +
      (∑ i ∈ A.filter (fun i => i ∉ B), f i) :=
    (Finset.sum_filter_add_sum_filter_not A (fun i => i ∈ B) f).symm
  rw [hsplit, hfilter]
  have hrest : (∑ i ∈ A.filter (fun i => i ∉ B), f i) ≤ 0 :=
    Finset.sum_nonpos fun i hi => hf i (Finset.mem_filter.mp hi).1
  linarith

/-- **The Anderson--Cappelletti--Kim--Nguyen drift for a one-species network.**

Let `N` be a strongly endotactic network over a single species, `κ` its rate constants, and let
`r₀` be a reaction whose source complex is of maximal molecularity `m` and which descends the
total-count tier strictly.  Then the total count satisfies the multiplicative Foster--Lyapunov
drift `Q V (n) ≤ -c · V (n) + K` with `c > 0` and `K ≥ 0`, where `V (n) = n`.

The mechanism: every ascending reaction has source of molecularity `≤ m - 1`, so its propensity
is bounded by a polynomial of degree `m - 1`, while the descending reaction `r₀` has a propensity
of degree `m`, which beats the ascending ones for large counts. -/
theorem drift_le {N : Network (Fin 1)} {κ : N.RateConstants}
    (hse : N.StronglyEndotacticStd)
    (r₀ : N.R) (hmax : N.IsMaxSource (fun _ => (1 : ℝ)) r₀)
    (hneg : N.wRate (fun _ => (1 : ℝ)) r₀ < 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : Fin 1 → ℕ, N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤
        -c * linearObservable (fun _ => (1 : ℝ)) n + K := by
  classical
  -- the tier drop of the descending reaction `r₀`
  have hdrop : tierDrop N r₀ < 0 := by simpa [wRate_total] using hneg
  -- the maximal molecularity `m` of the network is at least one
  have hm1 : 1 ≤ srcMol N r₀ := by
    have h2 : (N.reaction r₀).target 0 < (N.reaction r₀).source 0 := by
      have h3 : ((N.reaction r₀).target 0 : ℝ) < ((N.reaction r₀).source 0 : ℝ) := by
        simpa [tierDrop] using hdrop
      exact (Nat.cast_lt).mp h3
    unfold srcMol
    omega
  -- every source complex has molecularity at most `m`
  have hmax' : ∀ r' : N.R, srcMol N r' ≤ srcMol N r₀ := by
    intro r'
    have h1 := hmax r'
    rw [wValue_total, wValue_total] at h1
    exact (Nat.cast_le).mp h1
  -- the ascending reactions of the total-count direction
  set A : Finset N.R := Finset.univ.filter fun r => 0 < tierDrop N r with hAdef
  have hAmem : ∀ r : N.R, r ∈ A ↔ 0 < tierDrop N r := by
    intro r
    show r ∈ Finset.univ.filter (fun r => 0 < tierDrop N r) ↔ 0 < tierDrop N r
    simp
  -- the total ascending rate
  set C : ℝ := ∑ r ∈ A, κ.k r * tierDrop N r with hCdef
  have hCnonneg : 0 ≤ C := by
    rw [hCdef]
    exact Finset.sum_nonneg fun r hr => by
      have h1 := (hAmem r).mp hr
      exact mul_nonneg (κ.positive r).le h1.le
  -- the rate capacity of the descending reaction `r₀`
  set β : ℝ := κ.k r₀ * (-tierDrop N r₀) with hβdef
  have hβpos : 0 < β := by
    have h1 : (0 : ℝ) < κ.k r₀ := κ.positive r₀
    have h2 : (0 : ℝ) < -tierDrop N r₀ := by linarith
    rw [hβdef]
    exact mul_pos h1 h2
  -- every ascending reaction has source of molecularity at most `m - 1`
  have hmol : ∀ r ∈ A, srcMol N r ≤ srcMol N r₀ - 1 := by
    intro r hr
    have h1 : 0 < tierDrop N r := (hAmem r).mp hr
    have h2 : ¬ N.IsMaxSource (fun _ => (1 : ℝ)) r := by
      intro hmaxr
      have h3 := hse.1 (fun _ => (1 : ℝ)) r hmaxr
      rw [wRate_total] at h3
      linarith
    have h3 : srcMol N r < srcMol N r₀ := by
      have h4 : srcMol N r ≤ srcMol N r₀ := hmax' r
      by_contra hcon
      have h5 : srcMol N r₀ ≤ srcMol N r := by omega
      exact h2 (by
        rw [isMaxSource_iff]
        intro r'
        rcases Nat.eq_or_lt_of_le (hmax' r') with heq | hlt
        · rw [heq]; omega
        · omega)
    omega
  -- the descending reactions of the total-count direction do not ascend
  have hdesc : ∀ r : N.R, r ∉ A → tierDrop N r ≤ 0 := by
    intro r hr
    by_contra hcon
    have h1 : 0 < tierDrop N r := by linarith
    exact hr ((hAmem r).mpr h1)
  -- the estimate of the drift
  have hdrift : ∀ (n : Fin 1 → ℕ) (M : ℝ),
      (∀ r ∈ A, ((countDescFactorial (N.reaction r).source n : ℝ)) ≤ M) →
      (∑ r : N.R, (κ.k r) * ((countDescFactorial (N.reaction r).source n : ℝ)) * tierDrop N r)
        ≤ C * M
          + (κ.k r₀) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) * tierDrop N r₀ := by
    intro n M hM
    set f : N.R → ℝ := fun r =>
      (κ.k r) * ((countDescFactorial (N.reaction r).source n : ℝ)) * tierDrop N r with hfdef
    have hr₀mem : r₀ ∉ A := by
      intro hmem
      have h1 := (hAmem r₀).mp hmem
      linarith
    -- the ascending part
    have hA : (∑ r ∈ A, f r) ≤ C * M := by
      rw [hCdef]
      have h1 : (∑ r ∈ A, f r) ≤ ∑ r ∈ A, (κ.k r * tierDrop N r) * M := by
        refine Finset.sum_le_sum fun r hr => ?_
        have h2 := hM r hr
        have h3 : (0 : ℝ) ≤ κ.k r * tierDrop N r := by
          have h4 := (hAmem r).mp hr
          exact mul_nonneg (κ.positive r).le h4.le
        calc (κ.k r) * ((countDescFactorial (N.reaction r).source n : ℝ)) * tierDrop N r
            ≤ (κ.k r) * M * tierDrop N r := by
              have h4 : (0 : ℝ) ≤ tierDrop N r := (hAmem r).mp hr |>.le
              have h5 : (κ.k r) * ((countDescFactorial (N.reaction r).source n : ℝ)) ≤
                  (κ.k r) * M := mul_le_mul_of_nonneg_left h2 (κ.positive r).le
              exact mul_le_mul_of_nonneg_right h5 h4
            _ = (κ.k r * tierDrop N r) * M := by ring
      have h2 : (∑ r ∈ A, (κ.k r * tierDrop N r) * M) = (∑ r ∈ A, κ.k r * tierDrop N r) * M := by
        rw [Finset.sum_mul]
      linarith
    -- the descending part
    have hD : (∑ r ∈ (Finset.univ : Finset N.R) \ A, f r) ≤ f r₀ := by
      have hX : (∑ r ∈ (Finset.univ : Finset N.R) \ A, f r) ≤ ∑ r ∈ {r₀}, f r := by
        refine sum_le_sum_of_subset_of_nonpos f ((Finset.univ : Finset N.R) \ A) {r₀} ?_ ?_
        · intro r hr
          simp only [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ r, ?_⟩
          rw [Finset.mem_singleton] at hr
          subst hr
          exact hr₀mem
        · intro r hr
          have h1 : tierDrop N r ≤ 0 := hdesc r (fun h2 => (Finset.mem_sdiff.mp hr).2 h2)
          have h2 : (0 : ℝ) ≤ (κ.k r) * ((countDescFactorial (N.reaction r).source n : ℝ)) := by
            exact mul_nonneg (κ.positive r).le (by positivity)
          simp only [hfdef]
          exact mul_nonpos_of_nonneg_of_nonpos h2 h1
      simpa only [Finset.sum_singleton] using hX
    -- the splitting
    have hsplit : (∑ r : N.R, f r) =
        (∑ r ∈ A, f r) + (∑ r ∈ (Finset.univ : Finset N.R) \ A, f r) := by
      have h1 := Finset.sum_sdiff (s₁ := A) (s₂ := (Finset.univ : Finset N.R)) (f := f)
        (Finset.subset_univ _)
      rw [add_comm] at h1
      exact h1.symm
    have h1 := hsplit
    have h2 := hA
    have h3 := hD
    simp only [hfdef]
    linarith
  -- the crude bound, valid for every count
  have hcrude : ∀ n : Fin 1 → ℕ,
      N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤
        C * (Nat.pow (n 0 + 1) (srcMol N r₀ - 1) : ℝ) := by
    intro n
    rw [observableGenerator_total]
    have hM' : ∀ r ∈ A, ((countDescFactorial (N.reaction r).source n : ℝ))
        ≤ (Nat.pow (n 0 + 1) (srcMol N r₀ - 1) : ℝ) := by
      intro r hr
      rw [countDescFactorial_src]
      have h3 : (n 0).descFactorial (srcMol N r) ≤ (n 0) ^ (srcMol N r) :=
        Nat.descFactorial_le_pow _ _
      have h4 : (n 0) ^ (srcMol N r) ≤ (n 0 + 1) ^ (srcMol N r) :=
        Nat.pow_le_pow_left (by omega) _
      have h5 : (n 0 + 1) ^ (srcMol N r) ≤ (n 0 + 1) ^ (srcMol N r₀ - 1) :=
        Nat.pow_le_pow_right (by omega) (hmol r hr)
      exact_mod_cast (h3.trans (h4.trans h5))
    have h1 := hdrift n (Nat.pow (n 0 + 1) (srcMol N r₀ - 1) : ℝ) hM'
    have h2 : (0 : ℝ) ≤ (κ.k r₀) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) := by
      exact mul_nonneg (κ.positive r₀).le (by positivity)
    have h3 : tierDrop N r₀ < 0 := hdrop
    have h4 : (κ.k r₀) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) * tierDrop N r₀ ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos h2 h3.le
    linarith
  -- the refined bound, valid when the count reaches the maximal molecularity
  have hrefined : ∀ (n : Fin 1 → ℕ), srcMol N r₀ - 1 ≤ n 0 →
      N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤
        C * ((n 0).descFactorial (srcMol N r₀ - 1) : ℝ)
          - β * ((n 0).descFactorial (srcMol N r₀) : ℝ) := by
    intro n hn
    rw [observableGenerator_total]
    have hM' : ∀ r ∈ A, ((countDescFactorial (N.reaction r).source n : ℝ))
        ≤ ((n 0).descFactorial (srcMol N r₀ - 1) : ℝ) := by
      intro r hr
      rw [countDescFactorial_src]
      have h3 : (n 0).descFactorial (srcMol N r) ≤ (n 0).descFactorial (srcMol N r₀ - 1) :=
        descFactorial_mono (hmol r hr) hn
      exact_mod_cast h3
    have h1 := hdrift n ((n 0).descFactorial (srcMol N r₀ - 1) : ℝ) hM'
    have h2 : (0 : ℝ) ≤ (κ.k r₀) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) := by
      exact mul_nonneg (κ.positive r₀).le (by positivity)
    have h3 : tierDrop N r₀ < 0 := hdrop
    have h4 : (κ.k r₀) * tierDrop N r₀ = -β := by
      rw [hβdef]
      ring
    have h6 : (κ.k r₀) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) * tierDrop N r₀
        = -β * ((countDescFactorial (N.reaction r₀).source n : ℝ)) := by
      calc (κ.k r₀) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) * tierDrop N r₀
          = (κ.k r₀ * tierDrop N r₀) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) := by ring
        _ = (-β) * ((countDescFactorial (N.reaction r₀).source n : ℝ)) := by rw [h4]
    have h7 : ((countDescFactorial (N.reaction r₀).source n : ℝ))
        = ((n 0).descFactorial (srcMol N r₀) : ℝ) := by
      rw [countDescFactorial_src]
    rw [h6, h7] at h1
    linarith
  -- the threshold above which the refined bound is negative
  set N₀ : ℕ := Nat.floor ((srcMol N r₀ - 1 : ℝ) + 2 * C / β) + 1 with hN₀def
  have hN₀big : (srcMol N r₀ - 1 : ℝ) + 2 * C / β < (N₀ : ℝ) := by
    have h1 : ((srcMol N r₀ - 1 : ℝ) + 2 * C / β)
        < (Nat.floor ((srcMol N r₀ - 1 : ℝ) + 2 * C / β) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h2 : (N₀ : ℝ) = (Nat.floor ((srcMol N r₀ - 1 : ℝ) + 2 * C / β) : ℝ) + 1 := by
      rw [hN₀def]
      push_cast
      ring
    rw [h2]
    exact h1
  have hratio : (0 : ℝ) ≤ 2 * C / β := by
    have h1 : (0 : ℝ) ≤ 2 * C := by linarith [hCnonneg]
    exact div_nonneg h1 (le_of_lt hβpos)
  have hN₀nat : srcMol N r₀ ≤ N₀ := by
    have h1 : ((srcMol N r₀ - 1 : ℕ) : ℝ) < (N₀ : ℝ) := by
      have h2 : ((srcMol N r₀ - 1 : ℕ) : ℝ) = (srcMol N r₀ : ℝ) - 1 := by
        simpa using (Nat.cast_sub (R := ℝ) hm1)
      linarith [hN₀big, hratio]
    have h2 : (srcMol N r₀ - 1 : ℕ) < (N₀ : ℕ) := by exact_mod_cast h1
    omega
  have hβhalf : (0 : ℝ) < β / 2 := div_pos hβpos (by norm_num)
  have hKnonneg : (0 : ℝ) ≤ C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ) := by
    exact mul_nonneg hCnonneg (by positivity)
  refine ⟨β / 2, hβhalf,
    C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ) + (β / 2) * ((N₀ : ℕ) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ) := hKnonneg
    have h2 : (0 : ℝ) ≤ (β / 2) * ((N₀ : ℕ) : ℝ) := by positivity
    linarith
  · intro n
    by_cases hthresh : N₀ ≤ n 0
    · -- the refined bound
      have hbig : srcMol N r₀ - 1 ≤ n 0 := by
        have h1 : srcMol N r₀ ≤ N₀ := hN₀nat
        omega
      have h1 := hrefined n hbig
      set A' : ℝ := ((n 0).descFactorial (srcMol N r₀ - 1) : ℝ) with hA'def
      set B' : ℝ := (n 0 : ℝ) - ((srcMol N r₀ - 1 : ℕ) : ℝ) with hB'def
      have hA'pos : 1 ≤ A' := by
        have h2 : srcMol N r₀ - 1 ≤ n 0 := hbig
        rw [hA'def]
        exact_mod_cast (Nat.descFactorial_pos).2 h2
      have hB'big : 2 * C / β ≤ B' := by
        have h2 : (N₀ : ℝ) - ((srcMol N r₀ - 1 : ℕ) : ℝ) > 2 * C / β := by
          have h3 : ((srcMol N r₀ - 1 : ℕ) : ℝ) = (srcMol N r₀ : ℝ) - 1 := by
            simpa using (Nat.cast_sub (R := ℝ) hm1)
          linarith [hN₀big]
        rw [hB'def]
        have h3 : ((srcMol N r₀ - 1 : ℕ) : ℝ) ≤ (n 0 : ℝ) := by exact_mod_cast hbig
        have h4 : (N₀ : ℝ) ≤ (n 0 : ℝ) := by exact_mod_cast hthresh
        linarith
      have hident : ((n 0).descFactorial (srcMol N r₀) : ℝ) = A' * B' := by
        have h2 : srcMol N r₀ = (srcMol N r₀ - 1) + 1 := by omega
        rw [h2, Nat.descFactorial_succ]
        have h5 : ((n 0 - (srcMol N r₀ - 1) : ℕ) : ℝ) =
            (n 0 : ℝ) - ((srcMol N r₀ - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega)]
        rw [Nat.cast_mul, h5, hA'def, hB'def]
        ring
      have hB'pos : 1 ≤ B' := by
        rw [hB'def]
        have h2 : (srcMol N r₀ : ℝ) ≤ (n 0 : ℝ) := by
          have h3 : srcMol N r₀ ≤ N₀ := hN₀nat
          have h3' : (srcMol N r₀ : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast h3
          have h4 : (N₀ : ℝ) ≤ (n 0 : ℝ) := by exact_mod_cast hthresh
          linarith
        have h3 : ((srcMol N r₀ - 1 : ℕ) : ℝ) = (srcMol N r₀ : ℝ) - 1 := by
          simpa using (Nat.cast_sub (R := ℝ) hm1)
        linarith
      have hCcap : C ≤ (β / 2) * B' := by
        have h2 : C ≤ (β / 2) * (2 * C / β) := by
          have h3 : (β / 2) * (2 * C / β) = C := by
            have h4 : (0:ℝ) < β := hβpos
            field_simp
          rw [h3]
        have h3 : (β / 2) * (2 * C / β) ≤ (β / 2) * B' :=
          mul_le_mul_of_nonneg_left hB'big hβhalf.le
        linarith
      -- the two real quantities that occur in the drift estimate
      rw [hident] at h1
      set P : ℝ := (β / 2) * (A' * B') with hPdef
      set Q : ℝ := (β / 2) * ((n 0 : ℝ) - ((srcMol N r₀ - 1 : ℕ) : ℝ)) with hQdef
      have h3 : (0 : ℝ) ≤ A' := by linarith [hA'pos]
      have h1' : N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤ C * A' - 2 * P := by
        have h2 : β * (A' * B') = 2 * P := by
          rw [hPdef]
          ring
        rw [h2] at h1
        exact h1
      have h7 : C * A' ≤ P := by
        have h8 : C * A' ≤ ((β / 2) * B') * A' := mul_le_mul_of_nonneg_right hCcap h3
        rw [hPdef]
        simpa [mul_assoc, mul_comm, mul_left_comm] using h8
      have h10 : Q ≤ P := by
        have h11 : (A' * B') ≥ (n 0 : ℝ) - ((srcMol N r₀ - 1 : ℕ) : ℝ) := by
          rw [← hident]
          have h12 : srcMol N r₀ = (srcMol N r₀ - 1) + 1 := by omega
          rw [h12, Nat.descFactorial_succ]
          have h13 : ((n 0 - (srcMol N r₀ - 1) : ℕ) : ℝ) =
              (n 0 : ℝ) - ((srcMol N r₀ - 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub (by omega)]
          rw [Nat.cast_mul, h13]
          have h14 : (0 : ℝ) ≤ (n 0 : ℝ) - ((srcMol N r₀ - 1 : ℕ) : ℝ) := by
            have h15 : ((srcMol N r₀ - 1 : ℕ) : ℝ) ≤ (n 0 : ℝ) := by exact_mod_cast hbig
            linarith
          have h16 := mul_le_mul_of_nonneg_left hA'pos h14
          simpa [mul_one] using h16
        rw [hQdef, hPdef]
        have h12 : (0 : ℝ) ≤ (β / 2) := le_of_lt hβhalf
        exact mul_le_mul_of_nonneg_left h11 h12
      have hmain' : N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤ -P := by
        linarith
      have hmain0 : N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤
          -(β / 2) * (n 0 : ℝ) + (β / 2) * ((srcMol N r₀ - 1 : ℕ) : ℝ) := by
        have h2 : -P ≤ -Q := neg_le_neg h10
        have h3 : -Q = -(β / 2) * (n 0 : ℝ) + (β / 2) * ((srcMol N r₀ - 1 : ℕ) : ℝ) := by
          rw [hQdef]
          ring
        calc N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤ -P := hmain'
          _ ≤ -Q := h2
          _ = -(β / 2) * (n 0 : ℝ) + (β / 2) * ((srcMol N r₀ - 1 : ℕ) : ℝ) := h3
      have hmain : N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤
          -(β / 2) * linearObservable (fun _ => (1 : ℝ)) n
            + (β / 2) * ((srcMol N r₀ - 1 : ℕ) : ℝ) := by
        rw [linearObservable_total]
        exact hmain0
      have hKbound : (β / 2) * ((srcMol N r₀ - 1 : ℕ) : ℝ) ≤ (β / 2) * ((N₀ : ℕ) : ℝ) := by
        have h1 : srcMol N r₀ - 1 ≤ N₀ := by omega
        have h2 : (0 : ℝ) ≤ β / 2 := le_of_lt hβhalf
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) h2
      linarith [hmain, hKbound, hKnonneg]
    · -- the crude bound
      have h1 := hcrude n
      have h2 : Nat.pow (n 0 + 1) (srcMol N r₀ - 1) ≤ Nat.pow N₀ (srcMol N r₀ - 1) := by
        have h3 : n 0 + 1 ≤ N₀ := by omega
        exact Nat.pow_le_pow_left h3 _
      have h4 : (C * (Nat.pow (n 0 + 1) (srcMol N r₀ - 1) : ℝ))
          ≤ C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h2) hCnonneg
      have h5 : (β / 2) * ((N₀ : ℕ) : ℝ)
          ≥ (β / 2) * linearObservable (fun _ => (1 : ℝ)) n := by
        have h6 : (N₀ : ℝ) ≥ (n 0 : ℝ) := by
          have h7 : n 0 ≤ N₀ := by omega
          exact_mod_cast h7
        have h7 : (n 0 : ℝ) = linearObservable (fun _ => (1 : ℝ)) n := by
          rw [linearObservable_total]
        rw [← h7]
        simpa [mul_comm] using (mul_le_mul_of_nonneg_right h6 (le_of_lt hβhalf))
      have h8 : (0 : ℝ) ≤ (-(β / 2) * linearObservable (fun _ => (1 : ℝ)) n
          + (β / 2) * ((N₀ : ℕ) : ℝ)) := by
        have h9 : (β / 2) * ((N₀ : ℕ) : ℝ) - (β / 2) * linearObservable (fun _ => (1 : ℝ)) n ≥ 0 := by
          linarith [h5]
        have h10 : (-(β / 2) * linearObservable (fun _ => (1 : ℝ)) n
            + (β / 2) * ((N₀ : ℕ) : ℝ)) = ((β / 2) * ((N₀ : ℕ) : ℝ)
            - (β / 2) * linearObservable (fun _ => (1 : ℝ)) n) := by ring
        rw [h10]
        exact h9
      have h11 : N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n
          ≤ C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ) := h1.trans h4
      have h12 : C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ)
          ≤ (C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ)
            + (-(β / 2) * linearObservable (fun _ => (1 : ℝ)) n))
            + ((β / 2) * ((N₀ : ℕ) : ℝ)) := by
        calc C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ)
            = C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ) + 0 := by ring
          _ ≤ C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ)
              + ((-(β / 2) * linearObservable (fun _ => (1 : ℝ)) n)
                + (β / 2) * ((N₀ : ℕ) : ℝ)) := by
              simpa using (le_add_of_nonneg_right
                (a := C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ)) h8)
          _ = (C * (Nat.pow N₀ (srcMol N r₀ - 1) : ℝ)
              + (-(β / 2) * linearObservable (fun _ => (1 : ℝ)) n))
              + ((β / 2) * ((N₀ : ℕ) : ℝ)) := by ring
      refine h11.trans ?_
      convert h12 using 1; ring

/-- **The Anderson--Cappelletti--Kim--Nguyen drift for a one-species strongly endotactic
network.**  If the total-count direction is stoichiometrically active — that is, if some
reaction changes the number of molecules — then the total count satisfies the multiplicative
Foster--Lyapunov drift `Q V (n) ≤ -c · V (n) + K` with `c > 0` and `K ≥ 0`. -/
theorem drift_le_stronglyEndotactic {N : Network (Fin 1)} {κ : N.RateConstants}
    (hse : N.StronglyEndotacticStd)
    (hact : ∃ r : N.R, N.wRate (fun _ => (1 : ℝ)) r ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : Fin 1 → ℕ, N.observableGenerator κ (linearObservable (fun _ => (1 : ℝ))) n ≤
        -c * linearObservable (fun _ => (1 : ℝ)) n + K := by
  obtain ⟨r₀, hmax, hneg⟩ := hse.2 (fun _ => (1 : ℝ)) hact
  exact drift_le hse r₀ hmax hneg

/-- The count-lattice Lyapunov function of the one-species drift is nonnegative. -/
theorem lyapunov_nonneg (n : Fin 1 → ℕ) :
    0 ≤ linearObservable (fun _ => (1 : ℝ)) n := by
  rw [linearObservable_total]
  exact Nat.cast_nonneg _

/-- The count-lattice Lyapunov function of the one-species drift has finite sublevel sets. -/
theorem lyapunov_finiteSublevel (R : ℝ) :
    {n : Fin 1 → ℕ | linearObservable (fun _ => (1 : ℝ)) n ≤ R}.Finite :=
  finite_linearObservable_le (S := Fin 1) (fun _ => (1 : ℝ))
    (by intro s; fin_cases s; norm_num) R

/-- **Non-explosion for a one-species strongly endotactic network.**  The stochastic mass-action
chain makes only finitely many jumps in a finite time interval. -/
theorem nonExplosion {N : Network (Fin 1)} {κ : N.RateConstants}
    (hse : N.StronglyEndotacticStd)
    (hact : ∃ r : N.R, N.wRate (fun _ => (1 : ℝ)) r ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (n : Fin 1 → ℕ) :
    HasSum (fun m => N.transition κ t n m) 1 := by
  obtain ⟨c, hc, K, hK, hdrift⟩ := drift_le_stronglyEndotactic hse hact
  refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable (fun _ => (1 : ℝ)))
    lyapunov_nonneg lyapunov_finiteSublevel (le_refl 0) hK (fun m => ?_) ht n
  rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable (fun _ => (1 : ℝ))) m]
  have h := hdrift m
  linarith [mul_nonneg hc.le (lyapunov_nonneg m)]

/-- **Positive recurrence for a one-species strongly endotactic network.**  The chain has a
stationary probability which charges every count, and the probability of being at the starting
count converges to a strictly positive limit. -/
theorem positiveRecurrence {N : Network (Fin 1)} {κ : N.RateConstants}
    (hse : N.StronglyEndotacticStd)
    (hact : ∃ r : N.R, N.wRate (fun _ => (1 : ℝ)) r ≠ 0)
    (hirr : ∀ a b : Fin 1 → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (Fin 1 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a : Fin 1 → ℕ, Tendsto (fun t => N.transition κ t a a) atTop (𝓝 (π a))) := by
  classical
  obtain ⟨c, hc, K, hK, hdrift⟩ := drift_le_stronglyEndotactic hse hact
  have hstoch : ∀ t, 0 ≤ t → ∀ c0 : Fin 1 → ℕ, HasSum (fun b => (N.jumpSystem κ).Pmin t c0 b) 1 := by
    intro t ht c0
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable (fun _ => (1 : ℝ)))
      lyapunov_nonneg lyapunov_finiteSublevel (le_refl 0) hK (fun m => ?_) ht c0
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable (fun _ => (1 : ℝ))) m]
    have h := hdrift m
    linarith [mul_nonneg hc.le (lyapunov_nonneg m)]
  have hfinf : ∀ R : ℝ, {x : Fin 1 → ℕ | c * linearObservable (fun _ => (1 : ℝ)) x ≤ R}.Finite := by
    intro R
    refine (lyapunov_finiteSublevel (R / c)).subset fun x hx => ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [le_div_iff₀ hc]
    linarith
  have hdrift' : ∀ x : Fin 1 → ℕ,
      (N.jumpSystem κ).drift (linearObservable (fun _ => (1 : ℝ))) x ≤
        -(c * linearObservable (fun _ => (1 : ℝ)) x) + K := by
    intro x
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable (fun _ => (1 : ℝ))) x]
    have h := hdrift x
    linarith
  obtain ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, -⟩ :=
    (N.jumpSystem κ).foster_lyapunov_ergodic (linearObservable (fun _ => (1 : ℝ)))
      (fun x => c * linearObservable (fun _ => (1 : ℝ)) x)
      lyapunov_nonneg (fun x => mul_nonneg hc.le (lyapunov_nonneg x)) hfinf hK
      hdrift' hstoch (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
      (fun _ _ _ _ => hirr _ _) (Set.mem_univ (fun _ => 0))
  refine ⟨π, hπ0, hπ1, hπinv, fun b => hπpos b (Set.mem_univ b), ?_⟩
  intro a
  have hlim : Tendsto (fun t => (N.jumpSystem κ).Pmin t a a) atTop (𝓝 (π a)) :=
    (N.jumpSystem κ).tendsto_Pmin_of_invariant
      (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ => hirr _ _)
      (fun t ht c0 _ => hstoch t ht c0) hπ0 (fun b h => (h (Set.mem_univ b)).elim) hπ1 hπinv
      (Set.mem_univ a) a
  simpa only [Network.transition] using hlim

/-- **Geometric ergodicity for a one-species strongly endotactic network.** -/
theorem geometricErgodic {N : Network (Fin 1)} {κ : N.RateConstants}
    (hse : N.StronglyEndotacticStd)
    (hact : ∃ r : N.R, N.wRate (fun _ => (1 : ℝ)) r ≠ 0)
    (hirr : ∀ a b : Fin 1 → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (Fin 1 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(N.jumpSystem κ).Pmin t a b - π b| *
            (1 + β * linearObservable (fun _ => (1 : ℝ)) b) ≤
          C₀ * (1 + linearObservable (fun _ => (1 : ℝ)) a) * ρ ^ ⌊t⌋₊ := by
  classical
  obtain ⟨c, hc, K, hK, hdrift⟩ := drift_le_stronglyEndotactic hse hact
  have hstoch : ∀ t, 0 ≤ t → ∀ x : Fin 1 → ℕ, HasSum (fun b => (N.jumpSystem κ).Pmin t x b) 1 := by
    intro t ht x
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable (fun _ => (1 : ℝ)))
      lyapunov_nonneg lyapunov_finiteSublevel (le_refl 0) hK (fun m => ?_) ht x
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable (fun _ => (1 : ℝ))) m]
    have h := hdrift m
    linarith [mul_nonneg hc.le (lyapunov_nonneg m)]
  have hdrift' : ∀ x : Fin 1 → ℕ,
      (N.jumpSystem κ).drift (linearObservable (fun _ => (1 : ℝ))) x ≤
        -c * linearObservable (fun _ => (1 : ℝ)) x + K := by
    intro x
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable (fun _ => (1 : ℝ))) x]
    exact hdrift x
  exact (N.jumpSystem κ).geometric_ergodic (linearObservable (fun _ => (1 : ℝ)))
    lyapunov_nonneg lyapunov_finiteSublevel hc hK hdrift' hstoch hirr

end OneSpecies

end Network
end CRNT
