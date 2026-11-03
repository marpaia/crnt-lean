import CRNT.LinearAlgebra.OrientedMatroid
import CRNT.Kinetics.Generalized

/-!
# Conformal decomposition into elementary vectors

The **elementary vectors** of a subspace `S ⊆ (ι → ℝ)` are its nonzero members of minimal
support: the circuits of the oriented matroid realized by `S`. Rockafellar's conformal
decomposition theorem states that every nonzero `v ∈ S` is a **conformal sum** of elementary
vectors of `S` — a sum `v = ∑ eₖ` in which every summand `eₖ` conforms to `v` (never points
the opposite way at any coordinate). This is the structural backbone of the sign-vector theory
of subspaces underlying the toric multistationarity sign condition.

The development proves, by strong induction on support size, the *single-step* support
reduction that drives the decomposition and the existence of a conforming elementary vector
inside the support of any nonzero member, then assembles the full conformal sum.

* `support v` — the coordinates where `v` is nonzero.
* `Elementary S e` — `e ∈ S`, `e ≠ 0`, and no nonzero member of `S` has strictly smaller
  support: the minimal-support circuits of `S`.
* `exists_elementary_subset` — every nonzero `v ∈ S` contains an elementary vector of `S` in
  its support.
* `ConfDom S v w` — `w` is a nonzero conforming dominator of `v` in `S`: in `S`, conformal to
  `v`, with support inside `support v` (the nonzero conforming cone of `v`).
* `exists_min_confDom` — a minimal-support conforming dominator: a circuit of the conformal cone.
* `exists_confDom_reduction` — the conformal reduction step: subtract a conforming multiple to
  strictly shrink the support while staying in `S` and conformal to `v`.
* `exists_conformalSum` — **Rockafellar's conformal decomposition**: every nonzero `v ∈ S` is a
  list-sum of conforming dominators of `v` in `S`.
* `sameSign_of_confDom_support_eq` — a full-support conforming dominator is `SameSign` with `v`,
  bridging the conformal cone to the Müller sign condition.

Depends on: `CRNT.LinearAlgebra.OrientedMatroid`,
`CRNT.Kinetics.Generalized`.
-/

namespace CRNT

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The **support** of a real vector: the finite set of coordinates where it is nonzero. -/
noncomputable def support (v : ι → ℝ) : Finset ι := Finset.univ.filter (fun i => v i ≠ 0)

@[simp] theorem mem_support {v : ι → ℝ} {i : ι} : i ∈ support v ↔ v i ≠ 0 := by
  classical simp [support]

theorem not_mem_support {v : ι → ℝ} {i : ι} (h : v i = 0) : i ∉ support v := by
  simp [mem_support, h]

@[simp] theorem support_zero : support (0 : ι → ℝ) = ∅ := by
  ext i; simp

theorem support_eq_empty_iff {v : ι → ℝ} : support v = ∅ ↔ v = 0 := by
  constructor
  · intro h; funext i; by_contra hi; exact (Finset.notMem_empty i) (h ▸ mem_support.mpr hi)
  · rintro rfl; simp

theorem support_nonempty_of_ne_zero {v : ι → ℝ} (h : v ≠ 0) : (support v).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]; exact fun he => h (support_eq_empty_iff.mp he)

theorem support_smul {t : ℝ} (ht : t ≠ 0) (v : ι → ℝ) :
    support (t • v) = support v := by
  ext i; simp [mem_support, Pi.smul_apply, smul_eq_mul, ht]

/-- An **elementary vector** (circuit) of a subspace `S`: a nonzero member whose support is
minimal — no nonzero member of `S` has a strictly smaller support. -/
def Elementary (S : Submodule ℝ (ι → ℝ)) (e : ι → ℝ) : Prop :=
  e ∈ S ∧ e ≠ 0 ∧ ∀ w ∈ S, w ≠ 0 → ¬ support w ⊂ support e

/-- **Every nonzero member of `S` contains an elementary vector in its support.** Among the
nonzero members of `S` whose support is contained in `support v`, one has minimal support
cardinality; that minimizer is elementary and sits inside `support v`. -/
theorem exists_elementary_subset {S : Submodule ℝ (ι → ℝ)} {v : ι → ℝ}
    (hv : v ∈ S) (hv0 : v ≠ 0) :
    ∃ e, Elementary S e ∧ support e ⊆ support v := by
  classical
  -- The nonempty family of candidate support sets among nonzero members of `S` inside `v`.
  let P : Finset ι → Prop := fun A => ∃ w ∈ S, w ≠ 0 ∧ support w = A ∧ A ⊆ support v
  have hPv : P (support v) := ⟨v, hv, hv0, rfl, Finset.Subset.refl _⟩
  -- Minimize support cardinality over candidates using well-founded recursion on ℕ.
  let cands : Finset (Finset ι) := (support v).powerset.filter P
  have hmem : support v ∈ cands := by
    rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨Finset.Subset.refl _, hPv⟩
  have hne : cands.Nonempty := ⟨_, hmem⟩
  obtain ⟨A, hA, hmin⟩ := cands.exists_min_image Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hAsub, w, hwS, hw0, hwA, _⟩ := hA
  refine ⟨w, ⟨hwS, hw0, ?_⟩, ?_⟩
  · intro u huS hu0 hssub
    -- `support u ⊂ support w = A`, contradicting minimality of `A`'s cardinality.
    have huA : support u ⊆ support v := (hwA ▸ hssub.subset).trans hAsub
    have hucand : support u ∈ cands := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨huA, u, huS, hu0, rfl, huA⟩
    have := hmin (support u) hucand
    have hlt : (support u).card < A.card := by
      rw [← hwA]; exact Finset.card_lt_card hssub
    omega
  · rw [hwA]; exact hAsub

/-- A vector **conformally dominated** by `v`: nonzero, in `S`, conformal to `v`, with support
inside `support v`. The conforming cone of `v` in `S`, restricted to nonzero members. -/
def ConfDom (S : Submodule ℝ (ι → ℝ)) (v w : ι → ℝ) : Prop :=
  w ∈ S ∧ w ≠ 0 ∧ Conformal v w ∧ support w ⊆ support v

theorem confDom_self {S : Submodule ℝ (ι → ℝ)} {v : ι → ℝ} (hv : v ∈ S) (hv0 : v ≠ 0) :
    ConfDom S v v :=
  ⟨hv, hv0, fun _ => mul_self_nonneg _, Finset.Subset.refl _⟩

/-- At a coordinate in its support, a conformal dominator of `v` strictly agrees in sign with
`v`, so the ratio `v i / e i` is strictly positive. -/
theorem ratio_pos_of_confDom {S : Submodule ℝ (ι → ℝ)} {v e : ι → ℝ}
    (he : ConfDom S v e) {i : ι} (hi : i ∈ support e) : 0 < v i / e i := by
  obtain ⟨_, _, hconf, hsub⟩ := he
  have hei : e i ≠ 0 := mem_support.mp hi
  have hvi : v i ≠ 0 := mem_support.mp (hsub hi)
  have hprod : 0 < v i * e i := lt_of_le_of_ne (hconf i) (by
    intro h; exact hvi (by
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact h'
      · exact absurd h' hei))
  exact div_pos_iff.mpr (by
    rcases lt_or_gt_of_ne hei with h | h
    · right; constructor
      · nlinarith [hprod]
      · exact h
    · left; exact ⟨by nlinarith [hprod], h⟩)

/-- **Conformal reduction step.** For nonzero `v ∈ S` there is a conforming dominator `e` and a
strictly positive `t` such that `v - t • e` lies in `S`, is again conformal to `v`, and has
strictly smaller support. Subtracting the smallest support-ratio multiple of `e` zeroes a
coordinate of `v` without flipping any sign. Iterating peels `v` into conforming pieces. -/
theorem exists_confDom_reduction {S : Submodule ℝ (ι → ℝ)} {v e : ι → ℝ}
    (hv : v ∈ S) (he : ConfDom S v e) :
    ∃ t : ℝ, 0 < t ∧ v - t • e ∈ S ∧
      Conformal v (v - t • e) ∧ support (v - t • e) ⊂ support v := by
  classical
  obtain ⟨heS, he0, hconf, hsub⟩ := he
  have hes : (support e).Nonempty := support_nonempty_of_ne_zero he0
  -- Minimize the strictly-positive ratio `v i / e i` over `support e`.
  obtain ⟨j, hj, hjmin⟩ := (support e).exists_min_image (fun i => v i / e i) hes
  set t : ℝ := v j / e j with ht
  have htpos : 0 < t := ratio_pos_of_confDom ⟨heS, he0, hconf, hsub⟩ hj
  -- Sign-preservation on `support e`: for `i ∈ support e`, `v i - t e i` keeps the sign of `v i`.
  have hconf' : Conformal v (v - t • e) := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i ∈ support e
    · have hri : t ≤ v i / e i := hjmin i hi
      have hei : e i ≠ 0 := mem_support.mp hi
      have hratio : 0 < v i / e i := ratio_pos_of_confDom ⟨heS, he0, hconf, hsub⟩ hi
      have hcancel : v i / e i * e i = v i := by field_simp
      -- `v i (v i - t e i) = v i² - t (v i e i)`; use `t ≤ v i/e i`.
      rcases lt_or_gt_of_ne hei with hneg | hpos
      · have hvneg : v i < 0 := by nlinarith [hcancel]
        nlinarith [mul_le_mul_of_nonpos_right hri hneg.le, hcancel]
      · have hvpos : 0 < v i := by nlinarith [hcancel]
        nlinarith [mul_le_mul_of_nonneg_right hri hpos.le, hcancel]
    · have hei : e i = 0 := by by_contra h; exact hi (mem_support.mpr h)
      rw [hei, mul_zero, sub_zero]; exact mul_self_nonneg _
  refine ⟨t, htpos, S.sub_mem hv (S.smul_mem _ heS), hconf', ?_⟩
  -- Support strictly shrinks: it stays inside `support v`, and loses the argmin `j`.
  refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨j, hsub hj, ?_⟩
  · -- The new support is inside `support v`: any coordinate where `v` vanishes also has `e = 0`.
    intro i hi
    rw [mem_support] at hi ⊢
    by_contra hvi
    have hvi0 : v i = 0 := hvi
    have hei : e i = 0 := by
      by_contra h
      exact (mem_support.mp (hsub (mem_support.mpr h))) hvi0
    apply hi
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvi0, hei]
  · -- The argmin coordinate `j` is removed: `v j - (v j / e j) e j = 0`.
    rw [mem_support, not_not]
    have hej : e j ≠ 0 := mem_support.mp hj
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ht]
    field_simp; ring

/-- **A minimal-support conforming dominator.** Among the conforming dominators of `v` in `S`,
one has minimal support cardinality. It is a *circuit of the conformal cone* of `v`: a nonzero
member of `S` conformal to `v` whose support is contained in `support v` and is minimal with
that property — no conforming dominator of `v` has strictly smaller support. -/
theorem exists_min_confDom {S : Submodule ℝ (ι → ℝ)} {v : ι → ℝ}
    (hv : v ∈ S) (hv0 : v ≠ 0) :
    ∃ e, ConfDom S v e ∧ ∀ w, ConfDom S v w → ¬ support w ⊂ support e := by
  classical
  let P : Finset ι → Prop := fun A => ∃ w, ConfDom S v w ∧ support w = A
  let cands : Finset (Finset ι) := (support v).powerset.filter P
  have hmem : support v ∈ cands := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, v, confDom_self hv hv0, rfl⟩
  obtain ⟨A, hA, hmin⟩ := cands.exists_min_image Finset.card ⟨_, hmem⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hAsub, e, hcd, heA⟩ := hA
  refine ⟨e, hcd, ?_⟩
  intro w hwcd hwss
  have hwcand : support w ∈ cands := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    have hwsub : support w ⊆ support v := hwcd.2.2.2
    exact ⟨hwsub, w, hwcd, rfl⟩
  have := hmin (support w) hwcand
  have hlt : (support w).card < A.card := by rw [← heA]; exact Finset.card_lt_card hwss
  omega

/-- A strictly-positive multiple of a conforming dominator is again one, with the same support
and the same minimality. -/
theorem confDom_smul {S : Submodule ℝ (ι → ℝ)} {v e : ι → ℝ} {t : ℝ} (ht : 0 < t)
    (he : ConfDom S v e) : ConfDom S v (t • e) := by
  obtain ⟨heS, he0, hconf, hsub⟩ := he
  refine ⟨S.smul_mem _ heS, ?_, ?_, ?_⟩
  · simp only [ne_eq, smul_eq_zero, not_or]; exact ⟨ht.ne', he0⟩
  · intro i; simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hconf i]
  · rw [support_smul ht.ne']; exact hsub

/-- A support-minimal conforming dominator is in fact a circuit of the ambient subspace.
Minimality in a fixed orthant is enough: if an arbitrary subspace vector had strictly
smaller support, orient it and move along that line until one coordinate of the dominator
hits zero without leaving the orthant. -/
theorem elementary_of_min_confDom
    {S : Submodule ℝ (ι → ℝ)} {v e : ι → ℝ}
    (he : ConfDom S v e)
    (hmin : ∀ w, ConfDom S v w → ¬ support w ⊂ support e) :
    Elementary S e := by
  classical
  refine ⟨he.1, he.2.1, ?_⟩
  intro w hwS hw0 hstrict
  have hwsub : support w ⊆ support e := hstrict.subset
  obtain ⟨j, hj⟩ : ∃ j : ι, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  have hej : e j ≠ 0 := mem_support.mp (hwsub (mem_support.mpr hj))
  let u : ι → ℝ := if 0 < e j * w j then w else -w
  have huS : u ∈ S := by
    dsimp [u]
    split_ifs
    · exact hwS
    · exact S.neg_mem hwS
  have hu0 : u ≠ 0 := by
    dsimp [u]
    split_ifs
    · exact hw0
    · simpa using hw0
  have husupp : support u = support w := by
    dsimp [u]
    split_ifs
    · rfl
    · rw [show -w = (-1 : ℝ) • w by ext i; simp]
      exact support_smul (by norm_num) w
  have husub : support u ⊆ support e := by simpa [husupp] using hwsub
  have hjprod : 0 < e j * u j := by
    dsimp [u]
    split_ifs with hpos
    · exact hpos
    · simp only [Pi.neg_apply]
      have hprodne : e j * w j ≠ 0 := mul_ne_zero hej hj
      have hneg : e j * w j < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hprodne
      nlinarith
  let P : Finset ι := Finset.univ.filter (fun i => 0 < e i * u i)
  have hPne : P.Nonempty := by
    refine ⟨j, ?_⟩
    simp [P, hjprod]
  obtain ⟨k, hkP, hkmin⟩ := P.exists_min_image (fun i => e i / u i) hPne
  have hkprod : 0 < e k * u k := by simpa [P] using (Finset.mem_filter.mp hkP).2
  have hek : e k ≠ 0 := by
    intro h
    simp [h] at hkprod
  have huk : u k ≠ 0 := by
    intro h
    simp [h] at hkprod
  let t : ℝ := e k / u k
  have htpos : 0 < t := by
    dsimp [t]
    rcases lt_or_gt_of_ne hek with hekn | hekp
    · have hukn : u k < 0 := by
        rcases lt_or_gt_of_ne huk with h | h
        · exact h
        · nlinarith [hkprod]
      exact div_pos_of_neg_of_neg hekn hukn
    · have hukp : 0 < u k := by
        rcases lt_or_gt_of_ne huk with h | h
        · nlinarith [hkprod]
        · exact h
      exact div_pos hekp hukp
  let q : ι → ℝ := e - t • u
  have hqS : q ∈ S := by
    dsimp [q]
    exact S.sub_mem he.1 (S.smul_mem t huS)
  have hqconf_e : Conformal e q := by
    intro i
    dsimp [q]
    change 0 ≤ e i * (e i - t * u i)
    by_cases hipos : 0 < e i * u i
    · have hiP : i ∈ P := by simp [P, hipos]
      have hminratio : e k / u k ≤ e i / u i := hkmin i hiP
      have hpnn : 0 ≤ e i * u i := hipos.le
      have hmul := mul_le_mul_of_nonneg_right hminratio hpnn
      have hui : u i ≠ 0 := by
        intro h
        simp [h] at hipos
      have hratio : (e i / u i) * (e i * u i) = e i ^ 2 := by
        field_simp
      have hleft : (e k / u k) * (e i * u i) = t * (e i * u i) := by rfl
      rw [hleft, hratio] at hmul
      nlinarith [sq_nonneg (e i)]
    · have hpnonpos : e i * u i ≤ 0 := le_of_not_gt hipos
      have htp : t * (e i * u i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hpnonpos
      nlinarith [sq_nonneg (e i)]
  have hqsupp : support q ⊆ support e := by
    intro i hiq
    rw [mem_support] at hiq ⊢
    intro hei
    have hui : u i = 0 := by
      by_contra hune
      exact (mem_support.mp (husub (mem_support.mpr hune))) hei
    apply hiq
    simp [q, hei, hui]
  have hqconf_v : Conformal v q := by
    intro i
    have hve := he.2.2.1 i
    have heq := hqconf_e i
    by_cases hei : e i = 0
    · have hqi : q i = 0 := by
        by_contra hne
        exact (mem_support.mp (hqsupp (mem_support.mpr hne))) hei
      simp [hqi]
    · rcases lt_or_gt_of_ne hei with hen | hep
      · have hvle : v i ≤ 0 := by nlinarith [hve]
        have hqle : q i ≤ 0 := by nlinarith [heq]
        exact mul_nonneg_of_nonpos_of_nonpos hvle hqle
      · have hvge : 0 ≤ v i := by nlinarith [hve]
        have hqge : 0 ≤ q i := by nlinarith [heq]
        exact mul_nonneg hvge hqge
  have hqsubv : support q ⊆ support v := hqsupp.trans he.2.2.2
  have hqk : q k = 0 := by
    simp [q, t, huk]
  have hk_not_q : k ∉ support q := not_mem_support hqk
  have hk_e : k ∈ support e := mem_support.mpr hek
  have hqstrict : support q ⊂ support e :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hqsupp, by
      intro heq
      exact hk_not_q (heq ▸ hk_e)⟩
  by_cases hq0 : q = 0
  · have heqtu : e = t • u := by
      apply sub_eq_zero.mp
      simpa [q] using hq0
    have hsupp_eu : support e = support u := by rw [heqtu, support_smul htpos.ne']
    have hsupp_we : support w = support e := by rw [← husupp, ← hsupp_eu]
    exact hstrict.ne hsupp_we
  · exact hmin q ⟨hqS, hq0, hqconf_v, hqsubv⟩ hqstrict

/-- **Conformal decomposition (Rockafellar).** Every nonzero `v ∈ S` is a list-sum of nonzero
conforming dominators of `v` in `S` — members of `S` that conform to `v` with support contained
in `support v`. Iterating the conformal reduction step peels off one minimal conforming piece at
a time, strictly shrinking the support; the sum reconstructs `v` exactly. The peeled pieces are
chosen of minimal support (circuits of the conformal cone, via `exists_min_confDom`). -/
theorem exists_conformalSum {S : Submodule ℝ (ι → ℝ)} :
    ∀ {v : ι → ℝ}, v ∈ S → v ≠ 0 →
      ∃ L : List (ι → ℝ), L.sum = v ∧ ∀ w ∈ L, ConfDom S v w := by
  classical
  have key : ∀ n : ℕ, ∀ {v : ι → ℝ}, v ∈ S → v ≠ 0 → (support v).card ≤ n →
      ∃ L : List (ι → ℝ), L.sum = v ∧ ∀ w ∈ L, ConfDom S v w := by
    intro n
    induction n with
    | zero =>
      intro v hv hv0 hcard
      exact absurd (Nat.le_zero.mp hcard)
        (Finset.card_ne_zero_of_mem (support_nonempty_of_ne_zero hv0).choose_spec)
    | succ n ih =>
      intro v hv hv0 _
      -- Pick a minimal conforming dominator `e` and peel a multiple `t • e` off `v`.
      obtain ⟨e, hecd, _⟩ := exists_min_confDom hv hv0
      obtain ⟨t, htpos, hmemS, hconf, hssub⟩ := exists_confDom_reduction hv hecd
      set r : ι → ℝ := v - t • e with hr
      have hpiece : ConfDom S v (t • e) := confDom_smul htpos hecd
      have hve : v = (t • e) + r := by rw [hr]; module
      by_cases hr0 : r = 0
      · refine ⟨[t • e], ?_, ?_⟩
        · rw [List.sum_singleton, hve, hr0, add_zero]
        · intro w hw; rw [List.mem_singleton] at hw; subst hw; exact hpiece
      · -- Recurse on the strictly-smaller remainder `r`, then prepend `t • e`.
        have hcardlt : (support r).card < (support v).card := Finset.card_lt_card hssub
        obtain ⟨L, hLsum, hLconf⟩ := ih hmemS hr0 (by omega)
        refine ⟨(t • e) :: L, ?_, ?_⟩
        · rw [List.sum_cons, hLsum, hve]
        · intro w hw
          rw [List.mem_cons] at hw
          rcases hw with hw | hw
          · subst hw; exact hpiece
          · -- Transport a conforming piece of `r` to a conforming piece of `v`.
            obtain ⟨hwS, hw0, hwconf, hwsub⟩ := hLconf w hw
            refine ⟨hwS, hw0, ?_, hwsub.trans hssub.subset⟩
            intro i
            have hwr := hwconf i
            by_cases hri : r i = 0
            · have hwi : w i = 0 := by
                by_contra h; exact (mem_support.mp (hwsub (mem_support.mpr h))) hri
              rw [hwi, mul_zero]
            · -- `r` conforms to `v`: `r i, v i` share sign; `w i` shares `r i`'s sign.
              have hrv : 0 ≤ v i * r i := hconf i
              have hvi : v i ≠ 0 := by
                intro h; rw [h, zero_mul] at hrv
                rcases lt_trichotomy (r i) 0 with hn | hz | hp
                · -- `v i = 0` and `i ∈ support r ⊆ support v` is impossible.
                  exact hri (absurd (hssub.subset (mem_support.mpr hri)) (by simp [h]))
                · exact hri hz
                · exact hri (absurd (hssub.subset (mem_support.mpr hri)) (by simp [h]))
              rcases lt_trichotomy (r i) 0 with hrneg | hrz | hrpos
              · have hvneg : v i < 0 := by
                  rcases lt_trichotomy (v i) 0 with h | h | h
                  · exact h
                  · exact absurd h hvi
                  · nlinarith [hrv]
                nlinarith [hwr]
              · exact absurd hrz hri
              · have hvpos : 0 < v i := by
                  rcases lt_trichotomy (v i) 0 with h | h | h
                  · nlinarith [hrv]
                  · exact absurd h hvi
                  · exact h
                nlinarith [hwr]
  intro v hv hv0
  exact key (support v).card hv hv0 (le_refl _)

/-- Nonzero scaling preserves elementary vectors. -/
theorem Elementary.smul_ne {S : Submodule ℝ (ι → ℝ)} {e : ι → ℝ}
    (he : Elementary S e) {t : ℝ} (ht : t ≠ 0) : Elementary S (t • e) := by
  refine ⟨S.smul_mem t he.1, smul_ne_zero ht he.2.1, ?_⟩
  intro w hwS hw0 hstrict
  have hsupp : support (t • e) = support e := support_smul ht e
  rw [hsupp] at hstrict
  exact he.2.2 w hwS hw0 hstrict

/-- Strong conformal decomposition into ambient circuits. -/
theorem exists_elementaryConformalSum {S : Submodule ℝ (ι → ℝ)} :
    ∀ {v : ι → ℝ}, v ∈ S → v ≠ 0 →
      ∃ L : List (ι → ℝ), L.sum = v ∧
        ∀ w ∈ L, Elementary S w ∧ ConfDom S v w := by
  classical
  have key : ∀ n : ℕ, ∀ {v : ι → ℝ}, v ∈ S → v ≠ 0 → (support v).card ≤ n →
      ∃ L : List (ι → ℝ), L.sum = v ∧
        ∀ w ∈ L, Elementary S w ∧ ConfDom S v w := by
    intro n
    induction n with
    | zero =>
      intro v hv hv0 hcard
      exact absurd (Nat.le_zero.mp hcard)
        (Finset.card_ne_zero_of_mem (support_nonempty_of_ne_zero hv0).choose_spec)
    | succ n ih =>
      intro v hv hv0 _
      obtain ⟨e, hecd, hemin⟩ := exists_min_confDom hv hv0
      have helem : Elementary S e := elementary_of_min_confDom hecd hemin
      obtain ⟨t, htpos, hmemS, hconf, hssub⟩ := exists_confDom_reduction hv hecd
      set r : ι → ℝ := v - t • e with hr
      have hpiececd : ConfDom S v (t • e) := confDom_smul htpos hecd
      have hpieceElem : Elementary S (t • e) := helem.smul_ne htpos.ne'
      have hve : v = (t • e) + r := by rw [hr]; module
      by_cases hr0 : r = 0
      · refine ⟨[t • e], ?_, ?_⟩
        · rw [List.sum_singleton, hve, hr0, add_zero]
        · intro w hw
          rw [List.mem_singleton] at hw
          subst w
          exact ⟨hpieceElem, hpiececd⟩
      · have hcardlt : (support r).card < (support v).card := Finset.card_lt_card hssub
        obtain ⟨L, hLsum, hL⟩ := ih hmemS hr0 (by omega)
        refine ⟨(t • e) :: L, ?_, ?_⟩
        · rw [List.sum_cons, hLsum, hve]
        · intro w hw
          rw [List.mem_cons] at hw
          rcases hw with hw | hw
          · subst w
            exact ⟨hpieceElem, hpiececd⟩
          · obtain ⟨hwElem, hwS, hw0, hwconf, hwsub⟩ := hL w hw
            refine ⟨hwElem, hwS, hw0, ?_, hwsub.trans hssub.subset⟩
            intro i
            have hwr := hwconf i
            by_cases hri : r i = 0
            · have hwi : w i = 0 := by
                by_contra h
                exact (mem_support.mp (hwsub (mem_support.mpr h))) hri
              rw [hwi, mul_zero]
            · have hrv : 0 ≤ v i * r i := hconf i
              have hvi : v i ≠ 0 := by
                intro h
                rw [h, zero_mul] at hrv
                exact hri (absurd (hssub.subset (mem_support.mpr hri)) (by simp [h]))
              rcases lt_trichotomy (r i) 0 with hrneg | hrz | hrpos
              · have hvneg : v i < 0 := by
                  rcases lt_trichotomy (v i) 0 with h | h | h
                  · exact h
                  · exact absurd h hvi
                  · nlinarith [hrv]
                nlinarith [hwr]
              · exact absurd hrz hri
              · have hvpos : 0 < v i := by
                  rcases lt_trichotomy (v i) 0 with h | h | h
                  · nlinarith [hrv]
                  · exact absurd h hvi
                  · exact h
                nlinarith [hwr]
  intro v hv hv0
  exact key (support v).card hv hv0 (le_refl _)

/-- **A full-support conforming dominator is sign-identical to `v`.** A vector conformal to `v`
whose support equals `support v` agrees with `v` in strict sign coordinatewise (`SameSign v w`).
This bridges the conformal cone to the `SameSign` predicate driving the Müller sign condition: a
conforming dominator that misses no coordinate of `v` is a witness of the same sign vector. -/
theorem sameSign_of_confDom_support_eq {S : Submodule ℝ (ι → ℝ)} {v w : ι → ℝ}
    (hw : ConfDom S v w) (hsupp : support w = support v) : SameSign v w := by
  obtain ⟨_, _, hconf, _⟩ := hw
  intro i
  by_cases hvi : v i = 0
  · -- Outside `support v`: also outside `support w`, so both sides are `0`.
    have hwi : w i = 0 := by
      by_contra h; exact (mem_support.mp (hsupp ▸ mem_support.mpr h)) hvi
    rw [hvi, hwi]; exact ⟨Iff.rfl, Iff.rfl⟩
  · -- Inside `support v`: also inside `support w`; conformality forces matching strict signs.
    have hwi : w i ≠ 0 := mem_support.mp (hsupp ▸ mem_support.mpr hvi)
    have hpos : 0 < v i * w i :=
      lt_of_le_of_ne (hconf i) (fun h => hwi (by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact absurd h' hvi
        · exact h'))
    constructor
    · constructor
      · intro hv0; nlinarith [hpos]
      · intro hw0; nlinarith [hpos]
    · constructor
      · intro hv0; nlinarith [hpos]
      · intro hw0; nlinarith [hpos]

end CRNT

namespace CRNT

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A support-minimal nonzero nonnegative vector in a coordinate subspace.  This is the
order-cone analogue of `Elementary`, tailored to `S ∩ ℝ_{≥0}^ι`. -/
def NonnegElementary (S : Submodule ℝ (ι → ℝ)) (e : ι → ℝ) : Prop :=
  e ∈ S ∧ e ≠ 0 ∧ (∀ i, 0 ≤ e i) ∧
    ∀ w, w ∈ S → w ≠ 0 → (∀ i, 0 ≤ w i) → support w ⊆ support e →
      support e ⊆ support w

/-- Support-minimality in the nonnegative part of a subspace already implies
support-minimality in the whole subspace. -/
theorem NonnegElementary.elementary
    {S : Submodule ℝ (ι → ℝ)} {e : ι → ℝ}
    (he : NonnegElementary S e) : Elementary S e := by
  classical
  refine ⟨he.1, he.2.1, ?_⟩
  intro w hwS hw0 hstrict
  have hwsub : support w ⊆ support e := hstrict.subset
  obtain ⟨j, hj⟩ : ∃ j : ι, w j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 (funext h)
  let u : ι → ℝ := if 0 < w j then w else -w
  have huS : u ∈ S := by
    dsimp [u]
    split_ifs
    · exact hwS
    · exact S.neg_mem hwS
  have hu0 : u ≠ 0 := by
    dsimp [u]
    split_ifs
    · exact hw0
    · simpa using hw0
  have husupp : support u = support w := by
    dsimp [u]
    split_ifs
    · rfl
    · rw [show -w = (-1 : ℝ) • w by ext i; simp]
      exact support_smul (by norm_num) w
  have husub : support u ⊆ support e := by simpa [husupp] using hwsub
  have hujpos : 0 < u j := by
    dsimp [u]
    split_ifs with hpos
    · exact hpos
    · simp only [Pi.neg_apply]
      have : w j < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hj
      linarith
  let P : Finset ι := Finset.univ.filter (fun i => 0 < u i)
  have hPne : P.Nonempty := by
    refine ⟨j, ?_⟩
    simp [P, hujpos]
  obtain ⟨k, hkP, hkmin⟩ := P.exists_min_image (fun i => e i / u i) hPne
  have hukpos : 0 < u k := by simpa [P] using (Finset.mem_filter.mp hkP).2
  have hk_usupp : k ∈ support u := mem_support.mpr hukpos.ne'
  have hek_ne : e k ≠ 0 := mem_support.mp (husub hk_usupp)
  have hekpos : 0 < e k := lt_of_le_of_ne (he.2.2.1 k) (Ne.symm hek_ne)
  let t : ℝ := e k / u k
  have htpos : 0 < t := by dsimp [t]; exact div_pos hekpos hukpos
  let q : ι → ℝ := e - t • u
  have hqS : q ∈ S := by
    dsimp [q]
    exact S.sub_mem he.1 (S.smul_mem t huS)
  have hqnn : ∀ i, 0 ≤ q i := by
    intro i
    dsimp [q]
    change 0 ≤ e i - t * u i
    by_cases hipos : 0 < u i
    · have hiP : i ∈ P := by simp [P, hipos]
      have hmin : e k / u k ≤ e i / u i := hkmin i hiP
      have hui : 0 < u i := hipos
      have hmul : (e k / u k) * u i ≤ e i := by
        have := (le_div_iff₀ hui).mp hmin
        simpa [mul_comm] using this
      simpa [t] using sub_nonneg.mpr hmul
    · have hui : u i ≤ 0 := le_of_not_gt hipos
      have hetu : t * u i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hui
      linarith [he.2.2.1 i]
  have hqsupp : support q ⊆ support e := by
    intro i hiq
    rw [mem_support] at hiq ⊢
    intro hei
    have hui : u i = 0 := by
      by_contra hune
      exact (mem_support.mp (husub (mem_support.mpr hune))) hei
    apply hiq
    simp [q, hei, hui]
  have hqk : q k = 0 := by
    simp [q, t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hukpos.ne']
  have hk_not_q : k ∉ support q := not_mem_support hqk
  have hk_e : k ∈ support e := mem_support.mpr hek_ne
  have hqstrict : support q ⊂ support e :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hqsupp, by
      intro heq
      exact hk_not_q (heq ▸ hk_e)⟩
  by_cases hq0 : q = 0
  · have heq : e = t • u := by
      apply sub_eq_zero.mp
      simpa [q] using hq0
    have hsupp_eu : support e = support u := by
      rw [heq, support_smul htpos.ne']
    have : support w = support e := by rw [← husupp, ← hsupp_eu]
    exact hstrict.ne this
  · have hrev := he.2.2.2 q hqS hq0 hqnn hqsupp
    exact hqstrict.ne (Finset.Subset.antisymm hqsupp hrev)

/-- A conforming dominator of a nonnegative vector is itself nonnegative. -/
theorem nonneg_of_confDom {S : Submodule ℝ (ι → ℝ)} {v e : ι → ℝ}
    (hvnn : ∀ i, 0 ≤ v i) (he : ConfDom S v e) : ∀ i, 0 ≤ e i := by
  intro i
  obtain ⟨_, _, hconf, hsub⟩ := he
  by_cases hvi : v i = 0
  · have hei : e i = 0 := by
      by_contra hne
      have hi : i ∈ support e := mem_support.mpr hne
      exact (mem_support.mp (hsub hi)) hvi
    simp [hei]
  · have hvpos : 0 < v i := lt_of_le_of_ne (hvnn i) (Ne.symm hvi)
    nlinarith [hconf i]

/-- Minimality inside the conformal cone of a nonnegative vector is exactly support
minimality in the nonnegative part of the ambient subspace. -/
theorem nonnegElementary_of_min_confDom {S : Submodule ℝ (ι → ℝ)} {v e : ι → ℝ}
    (hvnn : ∀ i, 0 ≤ v i)
    (he : ConfDom S v e)
    (hmin : ∀ w, ConfDom S v w → ¬ support w ⊂ support e) :
    NonnegElementary S e := by
  have henn := nonneg_of_confDom hvnn he
  refine ⟨he.1, he.2.1, henn, ?_⟩
  intro w hwS hw0 hwnn hsub
  have hwcd : ConfDom S v w := by
    refine ⟨hwS, hw0, ?_, hsub.trans he.2.2.2⟩
    intro i
    exact mul_nonneg (hvnn i) (hwnn i)
  have hnss := hmin w hwcd
  have hcard : (support e).card ≤ (support w).card := by
    by_contra hnot
    have hlt : (support w).card < (support e).card := Nat.lt_of_not_ge hnot
    exact hnss (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro heq
      rw [heq] at hlt
      exact Nat.lt_irrefl _ hlt⟩)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  exact heq.symm.subset

/-- **Nonnegative conformal decomposition.** Every nonzero nonnegative vector in a
coordinate subspace is a finite sum of support-minimal nonzero nonnegative vectors of
that subspace. Every summand is supported inside the original vector. -/
theorem exists_nonnegElementarySum {S : Submodule ℝ (ι → ℝ)} :
    ∀ {v : ι → ℝ}, v ∈ S → v ≠ 0 → (∀ i, 0 ≤ v i) →
      ∃ L : List (ι → ℝ), L.sum = v ∧
        ∀ w ∈ L, NonnegElementary S w ∧ support w ⊆ support v := by
  classical
  have key : ∀ n : ℕ, ∀ {v : ι → ℝ}, v ∈ S → v ≠ 0 → (∀ i, 0 ≤ v i) →
      (support v).card ≤ n →
      ∃ L : List (ι → ℝ), L.sum = v ∧
        ∀ w ∈ L, NonnegElementary S w ∧ support w ⊆ support v := by
    intro n
    induction n with
    | zero =>
      intro v hv hv0 hvnn hcard
      exact absurd (Nat.le_zero.mp hcard)
        (Finset.card_ne_zero_of_mem (support_nonempty_of_ne_zero hv0).choose_spec)
    | succ n ih =>
      intro v hv hv0 hvnn _
      obtain ⟨e, hecd, hemin⟩ := exists_min_confDom hv hv0
      have helem : NonnegElementary S e := nonnegElementary_of_min_confDom hvnn hecd hemin
      obtain ⟨t, htpos, hrS, hrconf, hrsub⟩ := exists_confDom_reduction hv hecd
      set r : ι → ℝ := v - t • e with hr
      have hpiece : NonnegElementary S (t • e) := by
        have htsupp : support (t • e) = support e := support_smul htpos.ne' e
        refine ⟨S.smul_mem t helem.1, ?_, ?_, ?_⟩
        · exact smul_ne_zero htpos.ne' helem.2.1
        · intro i
          simp only [Pi.smul_apply, smul_eq_mul]
          exact mul_nonneg htpos.le (helem.2.2.1 i)
        · intro w hwS hw0 hwnn hsub
          rw [htsupp] at hsub ⊢
          exact helem.2.2.2 w hwS hw0 hwnn hsub
      have hpieceSub : support (t • e) ⊆ support v := by
        rw [support_smul htpos.ne']
        exact hecd.2.2.2
      have hrnn : ∀ i, 0 ≤ r i := by
        intro i
        have hc := hrconf i
        by_cases hvi : v i = 0
        · have hri : r i = 0 := by
            by_contra hne
            exact (mem_support.mp (hrsub.subset (mem_support.mpr hne))) hvi
          simp [hri]
        · have hvpos : 0 < v i := lt_of_le_of_ne (hvnn i) (Ne.symm hvi)
          nlinarith
      have hve : v = (t • e) + r := by rw [hr]; module
      by_cases hr0 : r = 0
      · refine ⟨[t • e], ?_, ?_⟩
        · rw [List.sum_singleton, hve, hr0, add_zero]
        · intro w hw
          rw [List.mem_singleton] at hw
          subst w
          exact ⟨hpiece, hpieceSub⟩
      · have hcardlt : (support r).card < (support v).card := Finset.card_lt_card hrsub
        obtain ⟨L, hLsum, hL⟩ := ih hrS hr0 hrnn (by omega)
        refine ⟨(t • e) :: L, ?_, ?_⟩
        · rw [List.sum_cons, hLsum, hve]
        · intro w hw
          rw [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact ⟨hpiece, hpieceSub⟩
          · obtain ⟨hwElem, hwSub⟩ := hL w hw
            exact ⟨hwElem, hwSub.trans hrsub.subset⟩
  intro v hv hv0 hvnn
  exact key (support v).card hv hv0 hvnn (le_refl _)

/-- A support-minimal nonnegative subspace vector spans the entire nonnegative cone on
its support: every nonzero nonnegative subspace vector supported inside it is a strictly
positive scalar multiple. -/
theorem NonnegElementary.eq_pos_smul_of_support_subset
    {S : Submodule ℝ (ι → ℝ)} {e w : ι → ℝ}
    (he : NonnegElementary S e)
    (hwS : w ∈ S) (hw0 : w ≠ 0) (hwnn : ∀ i, 0 ≤ w i)
    (hsub : support w ⊆ support e) :
    ∃ t : ℝ, 0 < t ∧ e = t • w := by
  have hwcd : ConfDom S e w := by
    refine ⟨hwS, hw0, ?_, hsub⟩
    intro i
    exact mul_nonneg (he.2.2.1 i) (hwnn i)
  obtain ⟨t, ht, hrS, hrconf, hrsub⟩ := exists_confDom_reduction he.1 hwcd
  let r : ι → ℝ := e - t • w
  have hrnn : ∀ i, 0 ≤ r i := by
    intro i
    have hc := hrconf i
    by_cases hei : e i = 0
    · have hri : r i = 0 := by
        by_contra hne
        have himem : i ∈ support r := by
          simpa [r] using (mem_support.mpr hne)
        exact (mem_support.mp (hrsub.subset himem)) hei
      simp [hri]
    · have hepos : 0 < e i := lt_of_le_of_ne (he.2.2.1 i) (Ne.symm hei)
      change 0 ≤ (e - t • w) i
      have hc' : e i * (e - t • w) i ≥ 0 := hc
      nlinarith
  have hr0 : r = 0 := by
    by_contra hrne
    have hrev := he.2.2.2 r (by simpa [r] using hrS) hrne hrnn hrsub.subset
    have hne := (Finset.ssubset_iff_subset_ne.mp hrsub).2
    exact hne (Finset.Subset.antisymm hrsub.subset hrev)
  refine ⟨t, ht, ?_⟩
  have hzero : e - t • w = 0 := by simpa [r] using hr0
  exact sub_eq_zero.mp hzero

/-- Sum over the finite index type of list positions reproduces the list sum. -/
theorem sum_get_eq_list_sum (L : List (ι → ℝ)) :
    (∑ i : Fin L.length, L.get i) = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih => simpa [Fin.sum_univ_succ, ih]

end CRNT
