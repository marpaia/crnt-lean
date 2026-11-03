import CRNT.LinearAlgebra.PowerProductMonoFinset
import CRNT.Theorems.DeficiencyOne.MultiClass
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Equilibria.DetailedBalanceLinearStability
import CRNT.Deficiency.DeficiencyOneLocalize
import CRNT.Deficiency.DeficiencyOneStructure

/-!
# Infinitesimal deficiency-one kernel lemmas

Algebraic and order-theoretic lemmas used to prove nonsingularity of the mass-action
Jacobian on the stoichiometric tangent space under the deficiency-one hypotheses.
-/


namespace CRNT
open scoped BigOperators

theorem powerProd_logSum_deriv_neg_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q a : ι → ℝ) (a0 qmin β : ℝ)
    (ha0 : 0 < a0)
    (hsum : a0 + ∑ i ∈ s, a i = 0)
    (hqmin : ∀ i ∈ s, qmin ≤ q i)
    (hlevel : ∀ v : ℝ, 0 ≤ a0 + ∑ i ∈ s.filter (fun i => v < q i), a i)
    (hβ : -qmin < β) :
    ∑ i ∈ s, a i / (β + q i) < 0 := by
  classical
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hsum; simp only [Finset.sum_empty, add_zero] at hsum
      exact absurd hsum ha0.ne'
    · exact h
  set m := s.card with hm
  have hm1 : 1 ≤ m := hne.card_pos
  set E : Fin m ≃ {x // x ∈ s} := (s.equivFin).symm with hE
  set e0 : Fin m → ι := fun i => (E i : ι) with he0
  set σ : Equiv.Perm (Fin m) := Tuple.sort (fun i => - q (e0 i)) with hσ
  set G : Fin m ≃ {x // x ∈ s} := σ.trans E with hG
  set g : Fin m → ι := fun i => (G i : ι) with hg
  have hgmem : ∀ i, g i ∈ s := fun i => (G i).2
  have hginj : Function.Injective g := fun i j h => G.injective (Subtype.ext h)
  have hmono : Monotone ((fun i => - q (e0 i)) ∘ σ) := by
    rw [hσ]; exact Tuple.monotone_sort _
  have hanti : ∀ i j : Fin m, i ≤ j → q (g j) ≤ q (g i) := by
    intro i j hij
    have h := hmono hij
    simp only [Function.comp_apply] at h
    have hgi : g i = e0 (σ i) := by simp only [hg, hG, he0, Equiv.trans_apply]
    have hgj : g j = e0 (σ j) := by simp only [hg, hG, he0, Equiv.trans_apply]
    rw [hgi, hgj]; linarith [h]
  have hreindex_sum : ∀ f : ι → ℝ, ∑ i ∈ s, f i = ∑ i : Fin m, f (g i) := by
    intro f
    rw [← Finset.sum_coe_sort s f]
    exact (Equiv.sum_comp G (fun c => f (c : ι))).symm
  set qf : Fin (m + 1) → ℝ := Fin.cons 0 (fun i => q (g i)) with hqf
  set af : Fin (m + 1) → ℝ := Fin.cons a0 (fun i => a (g i)) with haf
  set qN : ℕ → ℝ := fun j => if h : j < m + 1 then qf ⟨j, h⟩ else 0 with hqN
  set aN : ℕ → ℝ := fun j => if h : j < m + 1 then af ⟨j, h⟩ else 0 with haN
  have haN0 : aN 0 = a0 := by simp [haN, af]
  have hqNs : ∀ i : Fin m, qN (i.val + 1) = q (g i) := by
    intro i
    have hlt : i.val + 1 < m + 1 := by omega
    simp only [hqN, dif_pos hlt]
    rw [show (⟨i.val + 1, hlt⟩ : Fin (m + 1)) = i.succ from Fin.ext rfl, hqf, Fin.cons_succ]
  have haNs : ∀ i : Fin m, aN (i.val + 1) = a (g i) := by
    intro i
    have hlt : i.val + 1 < m + 1 := by omega
    simp only [haN, dif_pos hlt]
    rw [show (⟨i.val + 1, hlt⟩ : Fin (m + 1)) = i.succ from Fin.ext rfl, haf, Fin.cons_succ]
  have hqNi : ∀ (i : ℕ) (hi1 : 1 ≤ i) (hib : i - 1 < m), qN i = q (g ⟨i - 1, hib⟩) := by
    intro i hi1 hib
    have key := hqNs ⟨i - 1, hib⟩
    have hval : (⟨i - 1, hib⟩ : Fin m).val + 1 = i := by
      have hv0 : (⟨i - 1, hib⟩ : Fin m).val = i - 1 := rfl
      omega
    rwa [hval] at key
  have hqAnti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m → qN j ≤ qN i := by
    intro i j hi1 hij hjm
    rw [hqNi i hi1 (by omega), hqNi j (by omega) (by omega)]
    exact hanti ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ (by simp only [Fin.mk_le_mk]; omega)
  have hsum' : ∑ i ∈ Finset.range (m + 1), aN i = 0 := by
    have h1 : ∑ i ∈ Finset.range (m + 1), aN i = ∑ i : Fin (m + 1), af i := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => aN j) (m + 1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [haN, dif_pos i.2]
    rw [h1, haf, Fin.sum_cons, ← hreindex_sum a]
    linarith [hsum]
  have hpartial : ∀ i, 1 ≤ i → i < m → qN (i + 1) < qN i →
      0 ≤ ∑ j ∈ Finset.range (i + 1), aN j := by
    intro i hi1 him hdrop
    have hib : i - 1 < m := by omega
    set ii : Fin m := ⟨i, him⟩ with hii
    have hv : qN (i + 1) = q (g ii) := hqNs ii
    have hdropi : q (g ii) < q (g ⟨i - 1, hib⟩) := by
      have h1 : qN i = q (g ⟨i - 1, hib⟩) := hqNi i hi1 hib
      rw [← hv, ← h1]; exact hdrop
    rw [Finset.sum_range_succ', haN0]
    have hbij : ∑ j ∈ Finset.range i, aN (j + 1)
        = ∑ c ∈ s.filter (fun c => q (g ii) < q c), a c := by
      refine Finset.sum_bij (fun j hj => g ⟨j, by rw [Finset.mem_range] at hj; omega⟩)
        ?_ ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [Finset.mem_filter]
        refine ⟨hgmem _, ?_⟩
        have hle : (⟨j, by omega⟩ : Fin m) ≤ ⟨i - 1, hib⟩ := by
          simp only [Fin.mk_le_mk]; omega
        have hh := hanti ⟨j, by omega⟩ ⟨i - 1, hib⟩ hle
        linarith [hdropi, hh]
      · intro j1 hj1 j2 hj2 heq
        have := hginj heq
        simpa using this
      · intro c hc
        rw [Finset.mem_filter] at hc
        obtain ⟨j, hj⟩ := G.surjective ⟨c, hc.1⟩
        have hgjc : g j = c := by simp only [hg, hj]
        refine ⟨j.val, ?_, ?_⟩
        · rw [Finset.mem_range]
          by_contra hji
          rw [not_lt] at hji
          have hle : ii ≤ j := by simp only [hii, Fin.le_def]; omega
          have hh := hanti ii j hle
          rw [hgjc] at hh
          linarith [hc.2]
        · exact (congrArg g (Fin.ext rfl)).trans hgjc
      · intro j hj
        rw [Finset.mem_range] at hj
        exact haNs ⟨j, by omega⟩
    rw [hbij]
    linarith [hlevel (q (g ii)), hv]
  have hden : ∀ i : ℕ, 1 ≤ i → i ≤ m → 0 < β + qN i := by
    intro i hi1 him
    have hqi : qmin ≤ qN i := by
      rw [hqNi i hi1 (by omega)]
      exact hqmin _ (hgmem _)
    linarith
  set dN : ℕ → ℝ := fun i => -(1 / (β + qN i)) with hdN
  have hdanti : ∀ i, 1 ≤ i → i < m → dN (i + 1) ≤ dN i := by
    intro i hi1 him
    have hA : 0 < β + qN (i + 1) := hden (i + 1) (by omega) (by omega)
    have hqle : qN (i + 1) ≤ qN i := hqAnti i (i + 1) hi1 (by omega) (by omega)
    have hAB : β + qN (i + 1) ≤ β + qN i := by linarith
    have hinv := one_div_le_one_div_of_le hA hAB
    simp only [hdN]
    linarith
  have hd1 : dN 1 < 0 := by
    have hp : 0 < 1 / (β + qN 1) := one_div_pos.mpr (hden 1 (by omega) hm1)
    simp only [hdN]
    linarith
  have hpartD : ∀ i, 1 ≤ i → i < m → dN (i + 1) < dN i →
      0 ≤ ∑ j ∈ Finset.range (i + 1), aN j := by
    intro i hi1 him hdrop
    apply hpartial i hi1 him
    have hle := hqAnti i (i + 1) hi1 (by omega) (by omega)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply (ne_of_lt hdrop)
      simp [hdN, heq]
  have hkey := sum_increment_mul_pos hm1 hdanti hd1 (by rw [haN0]; exact ha0) hsum' hpartD
  have hordered : (∑ i ∈ Finset.range m, aN (i + 1) / (β + qN (i + 1))) =
      ∑ c ∈ s, a c / (β + q c) := by
    rw [hreindex_sum (fun c => a c / (β + q c)),
      ← Fin.sum_univ_eq_sum_range (fun j => aN (j + 1) / (β + qN (j + 1))) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hqNs i, haNs i]
  have hneg : 0 < -(∑ i ∈ Finset.range m, aN (i + 1) / (β + qN (i + 1))) := by
    convert hkey using 1 <;> simp [dN, div_eq_mul_inv]
  rw [hordered] at hneg
  linarith

end CRNT


namespace CRNT
open scoped BigOperators

 theorem shiftedLogSum_deriv_neg {ι : Type*} [DecidableEq ι] (s U : Finset ι)
    (ystar b G : ι → ℝ)
    (hys : ∀ c ∈ s, 0 < ystar c)
    (ha0 : 0 < ∑ c ∈ U, G c)
    (hsum : (∑ c ∈ U, G c) + ∑ c ∈ s, G c = 0)
    (hlevel : ∀ v : ℝ,
      0 ≤ (∑ c ∈ U, G c) + ∑ c ∈ s.filter (fun c => v < b c / ystar c), G c)
    {β : ℝ} (hd : ∀ c ∈ s, - (b c / ystar c) < β) :
    ∑ c ∈ s, G c * ystar c / (β * ystar c + b c) < 0 := by
  classical
  set q : ι → ℝ := fun c => b c / ystar c with hq
  have hsne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hsum; simp only [Finset.sum_empty, add_zero] at hsum
      exact absurd hsum ha0.ne'
    · exact h
  obtain ⟨c0, hc0s, hmin⟩ := Finset.exists_min_image s q hsne
  have hβ : -q c0 < β := by simpa [q] using hd c0 hc0s
  have hder := powerProd_logSum_deriv_neg_finset s q G (∑ c ∈ U, G c) (q c0) β
    ha0 hsum hmin (by simpa [q] using hlevel) hβ
  have heq : (∑ c ∈ s, G c / (β + q c)) =
      ∑ c ∈ s, G c * ystar c / (β * ystar c + b c) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hy : ystar c ≠ 0 := (hys c hc).ne'
    simp only [q]
    field_simp
    <;> ring
  rw [heq] at hder
  exact hder

end CRNT


namespace CRNT
namespace Network
open scoped BigOperators
variable {S : Type} [DecidableEq S] [Fintype S]

theorem pairing_constant_of_restrictedKineticImage_tangent (N : Network S) (κ : RateConstants N)
    {x : Concentration S} (hxpos : x.Positive)
    {θ : Quotient N.linkedSetoid} {c0 : N.ComplexIdx}
    (hc0term : N.IsTerminalSLC c0.val) (hc0θ : N.classOf c0 = θ)
    (hSLθ : ∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → N.StronglyLinked c0.val c.val)
    {g : N.ComplexIdx → ℝ} (hg0 : g ≠ 0)
    (hgY : N.complexMap g = 0) (hgθ : ∀ c, N.classOf c ≠ θ → g c = 0)
    {cx cw : ℝ} (hcx0 : cx ≠ 0)
    (hAx : N.restrictToClass θ (N.kineticMap κ (N.complexMonomialVector x)) = cx • g)
    {p w : N.ComplexIdx → ℝ}
    (hwval : ∀ c, N.classOf c = θ → w c = N.complexMonomialVector x c * p c)
    (hAw : N.restrictToClass θ (N.kineticMap κ w) = cw • g)
    (hgp : ∑ c, g c * p c = 0) :
    ∃ K : ℝ, ∀ c, N.classOf c = θ → p c = K := by
  classical
  set Ψx := N.complexMonomialVector x with hΨxdef
  have hΨxpos : ∀ c, 0 < Ψx c := fun c => Complex.massActionMonomial_pos hxpos c.val
  -- block diagonality: the restricted kinetic image is the kinetic image of the restriction
  set zx := N.restrictToClass θ Ψx with hzxdef
  have hAzx : N.kineticMap κ zx = cx • g := by rw [hzxdef, N.kineticMap_restrictToClass, hAx]
  -- `g` (hence `cx • g`) is supported on `θ`
  have hgθ' : ∀ c, N.classOf c ≠ θ → (cx • g) c = 0 := by
    intro c hc; simp only [Pi.smul_apply, smul_eq_mul, hgθ c hc, mul_zero]
  -- `StronglyLinked c0` lies inside `θ`.
  have hSLθ' : ∀ c, N.StronglyLinked c0.val c.val → N.classOf c = θ := by
    intro c hsl
    have : N.classOf c0 = N.classOf c := Quotient.sound (Linked.of_reaches hsl.1)
    rw [← this]; exact hc0θ
  -- the terminal-class kernel mode
  obtain ⟨b, hbpos, hboff, hbker⟩ := N.exists_pos_kernelVector_on_terminalSLC κ hc0term
  have hbnn : ∀ c, 0 ≤ b c := by
    intro c
    by_cases hsl : N.StronglyLinked c0.val c.val
    · exact (hbpos c hsl).le
    · rw [hboff c hsl]
  -- on `θ`, `zx` agrees with `Ψx`; off `θ`, `zx = 0`
  have hzxθ : ∀ c, N.classOf c = θ → zx c = Ψx c :=
    fun c hcq => by rw [hzxdef, restrictToClass_apply_of_eq _ _ hcq]
  have hzxoff : ∀ c, N.classOf c ≠ θ → zx c = 0 :=
    fun c hcq => by rw [hzxdef, restrictToClass_apply_of_ne _ _ hcq]
  -- the structured preimage `y* = zx − t·b`
  obtain ⟨ystar, cm, hAys, hcmsl, hcm0, hynnSL, hyoffSL⟩ :=
    N.exists_zeroCoord_preimage κ b zx hbpos hboff hbker
  have hG : N.kineticMap κ ystar = cx • g := by rw [hAys]; exact hAzx
  have hGθ : ∀ c, N.classOf c ≠ θ → N.kineticMap κ ystar c = 0 := by
    intro c hc; rw [hG]; exact hgθ' c hc
  -- `y* ≥ 0` everywhere.
  have hynn : ∀ c, 0 ≤ ystar c := by
    intro c
    by_cases hsl : N.StronglyLinked c0.val c.val
    · exact hynnSL c hsl
    · rw [hyoffSL c hsl]
      by_cases hcq : N.classOf c = θ
      · rw [hzxθ c hcq]; exact (hΨxpos c).le
      · rw [hzxoff c hcq]
  -- within `θ`, the zero set of `y*` sits inside `StronglyLinked c0`.
  have hUsl : ∀ c, N.classOf c = θ → ystar c = 0 → N.StronglyLinked c0.val c.val := by
    intro c hcq hc; by_contra hsl
    rw [hyoffSL c hsl, hzxθ c hcq] at hc; exact absurd hc (hΨxpos c).ne'
  -- `b > 0 ↔ StronglyLinked c0`.
  have hbpos_iff : ∀ c, 0 < b c ↔ N.StronglyLinked c0.val c.val := by
    intro c
    constructor
    · intro h; by_contra hsl; rw [hboff c hsl] at h; exact absurd h (lt_irrefl 0)
    · exact hbpos c
  -- exponent sum is zero
  have hGsum : ∑ c, N.kineticMap κ ystar c = 0 := N.kineticMap_sum_eq_zero κ ystar
  -- the toric orthogonality `⟨g, log Ψ⟩ = 0`
  have hortho : ∀ {z : Concentration S}, z.Positive →
      ∑ c, g c * Real.log (N.complexMonomialVector z c) = 0 := by
    intro z hz
    have : ∀ c, g c * Real.log (N.complexMonomialVector z c)
        = ∑ s, g c * ((c.val s : ℝ) * Real.log (z s)) := by
      intro c
      rw [N.log_complexMonomialVector hz c, Finset.mul_sum]
    simp only [this]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s _
    have : ∑ c, g c * ((c.val s : ℝ) * Real.log (z s))
        = (∑ c, g c * (c.val s : ℝ)) * Real.log (z s) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [this]
    have hY : ∑ c, g c * (c.val s : ℝ) = 0 := by
      have := congrFun hgY s
      simpa [N.complexMap_apply] using this
    rw [hY, zero_mul]
  -- per-class kernel uniqueness: any kernel vector is `s·b` on `θ`
  have hkeruniq : ∀ w : N.ComplexIdx → ℝ, N.kineticMap κ w = 0 →
      ∃ s : ℝ, ∀ c, N.classOf c = θ → w c = s * b c := by
    intro w hw
    have hvker : N.kineticMap κ (N.restrictToClass θ w) = 0 := by
      rw [N.kineticMap_restrictToClass, hw]
      funext c; by_cases hcq : N.classOf c = θ <;>
        simp [restrictToClass_apply_of_eq, restrictToClass_apply_of_ne, hcq]
    have hvoff : ∀ c, ¬ N.StronglyLinked c0.val c.val → N.restrictToClass θ w c = 0 := by
      intro c hsl
      by_cases hcq : N.classOf c = θ
      · have hcnt : ¬ N.IsTerminalSLC c.val := fun ht => hsl (hSLθ c hcq ht)
        rw [restrictToClass_apply_of_eq _ _ hcq]
        exact N.kineticMap_eq_zero_of_not_terminal κ hw hcnt
      · exact restrictToClass_apply_of_ne _ _ hcq
    obtain ⟨s, hs⟩ := N.terminalSLC_kernel_unique κ hbpos hboff hbker hvoff hvker
    refine ⟨s, fun c hcq => ?_⟩
    have := congrFun hs c
    rwa [restrictToClass_apply_of_eq _ _ hcq, Pi.smul_apply, smul_eq_mul] at this
  -- `Ψx = ystar + t·b` on `θ` (`zx = Ψx` there)
  have hwxker : N.kineticMap κ (zx - ystar) = 0 := by
    rw [map_sub, hAys, sub_self]
  obtain ⟨t, ht⟩ := hkeruniq (zx - ystar) hwxker
  have htval : ∀ c, N.classOf c = θ → Ψx c = ystar c + t * b c := by
    intro c hcq; have := ht c hcq; simp only [Pi.sub_apply] at this
    rw [hzxθ c hcq] at this; linarith [this]
  -- the tangent complex vector has the same affine preimage form on `θ`
  have hwker : N.kineticMap κ (N.restrictToClass θ w - (cw / cx) • ystar) = 0 := by
    rw [map_sub, map_smul, hG]
    rw [N.kineticMap_restrictToClass, hAw, smul_smul,
      show cw / cx * cx = cw from div_mul_cancel₀ cw hcx0, sub_self]
  obtain ⟨γ, hγ⟩ := hkeruniq (N.restrictToClass θ w - (cw / cx) • ystar) hwker
  have hγval : ∀ c, N.classOf c = θ → w c = cw / cx * ystar c + γ * b c := by
    intro c hcq; have hh := hγ c hcq
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hh
    rw [restrictToClass_apply_of_eq _ _ hcq] at hh
    linarith [hh]
  have hcmθ : N.classOf cm = θ := hSLθ' cm hcmsl
  have hbcm : 0 < b cm := hbpos cm hcmsl
  have htpos : 0 < t := by
    have hh := htval cm hcmθ
    rw [hcm0, zero_add] at hh
    have hx := hΨxpos cm
    nlinarith [hh, hx, hbcm]
  set βx : ℝ := 1 / t with hβx
  have hβxc : ∀ c, N.classOf c = θ → βx * ystar c + b c = Ψx c / t := by
    intro c hcq; rw [htval c hcq, hβx]; field_simp
  -- the index sets over the deficient class
  set sS : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = θ ∧ 0 < ystar c)
    with hsS
  set US : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = θ ∧ ystar c = 0)
    with hUS
  have hmems : ∀ c, c ∈ sS ↔ N.classOf c = θ ∧ 0 < ystar c := by
    intro c; rw [hsS, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  have hmemU : ∀ c, c ∈ US ↔ N.classOf c = θ ∧ ystar c = 0 := by
    intro c; rw [hUS, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  have hdisj : Disjoint sS US := by
    rw [Finset.disjoint_left]
    intro c hcs hcU
    exact absurd ((hmemU c).mp hcU).2 ((hmems c).mp hcs).2.ne'
  have hsuU : sS ∪ US = Finset.univ.filter (fun c => N.classOf c = θ) := by
    apply Finset.ext; intro c
    simp only [Finset.mem_union, hmems, hmemU, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hcq; rcases lt_or_eq_of_le (hynn c) with h | h
      · exact Or.inl ⟨hcq, h⟩
      · exact Or.inr ⟨hcq, h.symm⟩
  have hys : ∀ c ∈ sS, 0 < ystar c := fun c hc => ((hmems c).mp hc).2
  have hyU : ∀ c ∈ US, ystar c = 0 := fun c hc => ((hmemU c).mp hc).2
  -- `b > 0` exactly on the zero set within `θ`.
  have hUbpos : ∀ c, N.classOf c = θ → ystar c = 0 → 0 < b c :=
    fun c hcq hy0 => hbpos c (hUsl c hcq hy0)
  -- there is a complex of `θ` where `y*` is positive (else `g = 0`)
  have hc1 : ∃ c1 : N.ComplexIdx, N.classOf c1 = θ ∧ 0 < ystar c1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hy0 : ∀ c, N.classOf c = θ → ystar c = 0 :=
      fun c hcq => le_antisymm (hcon c hcq) (hynn c)
    apply hg0
    -- `A_k (zx) = cx • g`, but on `θ` `zx = t·b` (from `Ψx = ystar + t·b` and `ystar = 0`),
    -- and `zx` is supported on `θ`, so `A_k zx = t·A_k b = 0`, forcing `cx • g = 0`.
    have hrzx : zx = t • b := by
      funext c; by_cases hcq : N.classOf c = θ
      · rw [hzxθ c hcq, htval c hcq, hy0 c hcq, zero_add, Pi.smul_apply, smul_eq_mul]
      · rw [hzxoff c hcq, Pi.smul_apply, smul_eq_mul,
          hboff c (fun hsl => hcq (hSLθ' c hsl)), mul_zero]
    have hcxg : cx • g = 0 := by rw [← hAzx, hrzx, map_smul, hbker, smul_zero]
    exact (smul_eq_zero.mp hcxg).resolve_left hcx0
  obtain ⟨c1, hc1θ, hc1pos⟩ := hc1
  -- `a₀ > 0`: net inflow into the zero set from a `y*`-positive complex (a crossing reaction)
  have ha0 : 0 < ∑ c ∈ US, N.kineticMap κ ystar c := by
    obtain ⟨d, hreach, hdterm⟩ := N.exists_terminal_reachable c1
    have hdθ : N.classOf d = θ := by
      rw [← hc1θ]; exact (Quotient.sound (Linked.of_reaches hreach)).symm
    have hSLd : N.StronglyLinked c0.val d.val := hSLθ d hdθ hdterm
    have hreachcm : N.Reaches c1.val cm.val := hreach.trans (hSLd.2.trans hcmsl.1)
    obtain ⟨r₀, hns, hnt⟩ :=
      N.exists_crossing_reaction
        (fun c => ∃ h : c ∈ N.complexes, (⟨c, h⟩ : N.ComplexIdx) ∈ US) hreachcm
        (fun ⟨h, hmem⟩ => absurd ((hmemU _).mp hmem).2 hc1pos.ne')
        ⟨cm.property, (hmemU cm).mpr ⟨hcmθ, hcm0⟩⟩
    obtain ⟨ht, htmem⟩ := hnt
    have htgtU : N.targetIdx r₀ ∈ US := htmem
    have hsrcU : N.sourceIdx r₀ ∉ US := fun hmem => hns ⟨(N.sourceIdx r₀).property, hmem⟩
    have hsrcθ : N.classOf (N.sourceIdx r₀) = θ := by
      rw [N.classOf_sourceIdx_eq_targetIdx]; exact ((hmemU _).mp htgtU).1
    have hsrcpos : 0 < ystar (N.sourceIdx r₀) := by
      rcases lt_or_eq_of_le (hynn (N.sourceIdx r₀)) with hp | hp
      · exact hp
      · exact absurd ((hmemU _).mpr ⟨hsrcθ, hp.symm⟩) hsrcU
    exact N.sum_kineticMap_pos_of_inflow κ ystar US hynn hyU hsrcU htgtU hsrcpos
  -- the level set decomposes as a super-level set of `b − v·y*`
  have hcombine : ∀ v : ℝ,
      (∑ c ∈ US, N.kineticMap κ ystar c)
        + (∑ c ∈ sS.filter (fun c => v < b c / ystar c), N.kineticMap κ ystar c)
      = ∑ c ∈ Finset.univ.filter (fun c => v * ystar c < b c), N.kineticMap κ ystar c := by
    intro v
    have hdU : Disjoint (sS.filter (fun c => v < b c / ystar c)) US := by
      rw [Finset.disjoint_left]
      intro c hcs hcU
      have hpos : 0 < ystar c := ((hmems c).mp (Finset.mem_of_mem_filter c hcs)).2
      rw [((hmemU c).mp hcU).2] at hpos; exact lt_irrefl 0 hpos
    rw [add_comm, ← Finset.sum_union hdU]
    apply Finset.sum_subset
    · intro c hc
      rw [Finset.mem_filter]; refine ⟨Finset.mem_univ c, ?_⟩
      rw [Finset.mem_union] at hc
      rcases hc with hc | hc
      · have hyc : 0 < ystar c := ((hmems c).mp (Finset.mem_of_mem_filter c hc)).2
        exact (lt_div_iff₀ hyc).mp (Finset.mem_filter.mp hc).2
      · have hcU := (hmemU c).mp hc
        rw [hcU.2, mul_zero]; exact hUbpos c hcU.1 hcU.2
    · intro c hcuniv hc2
      by_contra hGc
      have hcθ : N.classOf c = θ := by by_contra h; exact hGc (hGθ c h)
      have hlt : v * ystar c < b c := (Finset.mem_filter.mp hcuniv).2
      rw [Finset.mem_union, not_or] at hc2
      rcases lt_or_eq_of_le (hynn c) with hyc | hyc
      · exact hc2.1 (Finset.mem_filter.mpr ⟨(hmems c).mpr ⟨hcθ, hyc⟩,
          (lt_div_iff₀ hyc).mpr hlt⟩)
      · exact hc2.2 ((hmemU c).mpr ⟨hcθ, hyc.symm⟩)
  -- the level-set sign in all three threshold regimes
  have hlevel : ∀ v : ℝ,
      0 ≤ (∑ c ∈ US, N.kineticMap κ ystar c)
        + ∑ c ∈ sS.filter (fun c => v < b c / ystar c), N.kineticMap κ ystar c := by
    intro v
    rw [hcombine v]
    rcases lt_trichotomy v 0 with hv | hv | hv
    · have heq : (∑ c ∈ Finset.univ.filter (fun c => v * ystar c < b c), N.kineticMap κ ystar c)
          = ∑ c, N.kineticMap κ ystar c := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro c _ hc2
        by_contra hGc
        have hcθ : N.classOf c = θ := by by_contra h; exact hGc (hGθ c h)
        refine hc2 (Finset.mem_filter.mpr ⟨Finset.mem_univ c, ?_⟩)
        by_cases hb : 0 < b c
        · nlinarith [mul_nonpos_of_nonpos_of_nonneg hv.le (hynn c)]
        · have hb0 : b c = 0 := le_antisymm (not_lt.mp hb) (hbnn c)
          have hsl : ¬ N.StronglyLinked c0.val c.val := fun h => hb (hbpos c h)
          have hyp : 0 < ystar c := by
            rcases lt_or_eq_of_le (hynn c) with hp | hp
            · exact hp
            · exact absurd (hUsl c hcθ hp.symm) hsl
          rw [hb0]; nlinarith [hyp]
      rw [heq, hGsum]
    · subst hv
      have hfeq : (Finset.univ.filter (fun c => (0 : ℝ) * ystar c < b c))
          = Finset.univ.filter (fun c => (0 : ℝ) < b c) := by
        apply Finset.filter_congr; intro c _; rw [zero_mul]
      rw [hfeq]
      apply N.sum_kineticMap_closed_nonneg κ ystar _ _ hynn
      intro r hsrc
      rw [Finset.mem_filter] at hsrc ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hsl : N.StronglyLinked c0.val (N.sourceIdx r).val := (hbpos_iff _).mp hsrc.2
      have hreachtgt : N.Reaches c0.val (N.targetIdx r).val := hsl.1.tail ⟨r, rfl, rfl⟩
      exact (hbpos_iff _).mpr (N.stronglyLinked_of_reaches_of_terminal hc0term hreachtgt)
    · exact N.sum_kineticMap_superlevel_nonneg κ b ystar hv hbker
  -- total exponent sum over the class is zero
  have hsum0 : (∑ c ∈ US, N.kineticMap κ ystar c) + ∑ c ∈ sS, N.kineticMap κ ystar c = 0 := by
    have huniv : (∑ c ∈ sS ∪ US, N.kineticMap κ ystar c) = 0 := by
      rw [hsuU]
      rw [show (∑ c ∈ Finset.univ.filter (fun c => N.classOf c = θ), N.kineticMap κ ystar c)
            = ∑ c, N.kineticMap κ ystar c from
          Finset.sum_subset (Finset.subset_univ _)
            (fun c _ hc => hGθ c (by simpa using hc)), hGsum]
    rw [Finset.sum_union hdisj] at huniv; linarith [huniv]
  -- domain membership for both parameters, from positivity of the monomials
  have hd₁ : ∀ c ∈ sS, - (b c / ystar c) < βx := by
    intro c hc
    have hcq : N.classOf c = θ := ((hmems c).mp hc).1
    have hyc : 0 < ystar c := ((hmems c).mp hc).2
    have hpos : 0 < βx * ystar c + b c := by rw [hβxc c hcq]; exact div_pos (hΨxpos c) htpos
    have key : 0 < βx + b c / ystar c := by
      rw [show βx + b c / ystar c = (βx * ystar c + b c) / ystar c by field_simp]
      exact div_pos hpos hyc
    linarith [key]
  have hDneg := shiftedLogSum_deriv_neg sS US ystar b (N.kineticMap κ ystar)
    hys ha0 hsum0 hlevel hd₁
  have hgsum : ∑ c, g c = 0 := by
    have hh := hGsum
    rw [show (∑ c, N.kineticMap κ ystar c) = cx * ∑ c, g c from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by
        rw [hG]
        simp only [Pi.smul_apply, smul_eq_mul]] at hh
    exact (mul_eq_zero.mp hh).resolve_left hcx0
  have hqrestrict : (∑ c, g c * ystar c / Ψx c) =
      ∑ c ∈ sS, g c * ystar c / Ψx c := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hcnot
    by_cases hcq : N.classOf c = θ
    · have hynpos : ¬ 0 < ystar c := by
        intro hyp
        exact hcnot ((hmems c).mpr ⟨hcq, hyp⟩)
      have hy0 : ystar c = 0 := le_antisymm (not_lt.mp hynpos) (hynn c)
      rw [hy0, mul_zero, zero_div]
    · rw [hgθ c hcq, zero_mul, zero_div]
  have hDform :
      (∑ c ∈ sS, N.kineticMap κ ystar c * ystar c /
          (βx * ystar c + b c)) =
        cx * t * (∑ c ∈ sS, g c * ystar c / Ψx c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hcq : N.classOf c = θ := ((hmems c).mp hc).1
    have hψ : Ψx c ≠ 0 := (hΨxpos c).ne'
    have ht0 : t ≠ 0 := htpos.ne'
    rw [hG]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hβxc c hcq]
    field_simp
  have hqne : (∑ c, g c * ystar c / Ψx c) ≠ 0 := by
    rw [hqrestrict]
    intro hzero
    rw [hDform, hzero, mul_zero] at hDneg
    exact (lt_irrefl 0) hDneg
  set A : ℝ := cw / cx with hA
  have hpraw : ∀ c, N.classOf c = θ →
      p c = γ / t + (A - γ / t) * (ystar c / Ψx c) := by
    intro c hcq
    have hw := hwval c hcq
    rw [hγval c hcq] at hw
    have htv := htval c hcq
    have hψ : Ψx c ≠ 0 := (hΨxpos c).ne'
    have ht0 : t ≠ 0 := htpos.ne'
    field_simp [ht0, hψ]
    rw [htv] at hw ⊢
    linear_combination -t * hw
  have hpform : ∀ c, g c * p c =
      (γ / t) * g c + (A - γ / t) * (g c * ystar c / Ψx c) := by
    intro c
    by_cases hcq : N.classOf c = θ
    · rw [hpraw c hcq]
      ring
    · rw [hgθ c hcq]
      simp
  have hcoeff : (A - γ / t) * (∑ c, g c * ystar c / Ψx c) = 0 := by
    have hh := hgp
    rw [show (∑ c, g c * p c) =
        (γ / t) * (∑ c, g c) +
          (A - γ / t) * (∑ c, g c * ystar c / Ψx c) from by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => hpform c] at hh
    rw [hgsum, mul_zero, zero_add] at hh
    exact hh
  have hcoefzero : A - γ / t = 0 := (mul_eq_zero.mp hcoeff).resolve_right hqne
  refine ⟨γ / t, fun c hcq => ?_⟩
  have hp := hpraw c hcq
  have hcoef : A = γ / t := sub_eq_zero.mp hcoefzero
  rw [hcoef, sub_self, zero_mul, add_zero] at hp
  exact hp

end Network
end CRNT


namespace CRNT
namespace Network
open scoped BigOperators
variable {S : Type} [DecidableEq S] [Fintype S]

theorem constant_on_class_of_stationary_weight
    (N : Network S) (κ : N.RateConstants)
    {θ : Quotient N.linkedSetoid} {u p : N.ComplexIdx → ℝ}
    (hunn : ∀ c, 0 ≤ u c)
    (hupos : ∀ c, N.classOf c = θ → 0 < u c)
    (hAu : N.kineticMap κ u = 0)
    (hpair : ∑ c, N.kineticMap κ (fun d => u d * p d) c * p c = 0) :
    ∀ c d, N.classOf c = θ → N.classOf d = θ → p c = p d := by
  classical
  have hstatSq : ∑ r : N.R, κ.k r * u (N.sourceIdx r) *
      (p (N.targetIdx r)^2 - p (N.sourceIdx r)^2) = 0 := by
    have hh := N.kineticMap_pairing κ u (fun c => p c ^ 2)
    rw [hAu] at hh
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hh
    exact hh.symm
  have hpairR : ∑ r : N.R, κ.k r * (u (N.sourceIdx r) * p (N.sourceIdx r)) *
      (p (N.targetIdx r) - p (N.sourceIdx r)) = 0 := by
    have hh := N.kineticMap_pairing κ (fun d => u d * p d) p
    exact hh.symm.trans hpair
  have hsquares : ∑ r : N.R, κ.k r * u (N.sourceIdx r) *
      (p (N.targetIdx r) - p (N.sourceIdx r))^2 = 0 := by
    have hid :
        (∑ r : N.R, κ.k r * u (N.sourceIdx r) *
          (p (N.targetIdx r) - p (N.sourceIdx r))^2) =
        (∑ r : N.R, κ.k r * u (N.sourceIdx r) *
          (p (N.targetIdx r)^2 - p (N.sourceIdx r)^2)) -
          2 * (∑ r : N.R, κ.k r * (u (N.sourceIdx r) * p (N.sourceIdx r)) *
            (p (N.targetIdx r) - p (N.sourceIdx r))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [hid, hstatSq, hpairR]
    ring
  have hedge : ∀ r : N.R, N.classOf (N.sourceIdx r) = θ →
      p (N.targetIdx r) = p (N.sourceIdx r) := by
    intro r hrs
    have hterm0 : κ.k r * u (N.sourceIdx r) *
        (p (N.targetIdx r) - p (N.sourceIdx r))^2 = 0 := by
      have hnonneg : ∀ q : N.R, 0 ≤ κ.k q * u (N.sourceIdx q) *
          (p (N.targetIdx q) - p (N.sourceIdx q))^2 := by
        intro q
        exact mul_nonneg (mul_nonneg (κ.positive q).le (hunn _)) (sq_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hnonneg q)).mp hsquares r
        (Finset.mem_univ r)
    have hk : 0 < κ.k r := κ.positive r
    have hu : 0 < u (N.sourceIdx r) := hupos _ hrs
    have hsq : (p (N.targetIdx r) - p (N.sourceIdx r))^2 = 0 := by
      rcases mul_eq_zero.mp hterm0 with h | h
      · rcases mul_eq_zero.mp h with hk0 | hu0
        · exact absurd hk0 hk.ne'
        · exact absurd hu0 hu.ne'
      · exact h
    nlinarith [sq_nonneg (p (N.targetIdx r) - p (N.sourceIdx r))]
  let pθ : N.ComplexIdx → ℝ := fun c => if N.classOf c = θ then p c else 0
  have hedgeAll : ∀ r : N.R, pθ (N.targetIdx r) = pθ (N.sourceIdx r) := by
    intro r
    by_cases hrs : N.classOf (N.sourceIdx r) = θ
    · have hrt : N.classOf (N.targetIdx r) = θ := by
        rw [← N.classOf_sourceIdx_eq_targetIdx]
        exact hrs
      simp only [pθ, if_pos hrs, if_pos hrt]
      exact hedge r hrs
    · have hrt : N.classOf (N.targetIdx r) ≠ θ := by
        intro h
        apply hrs
        rw [N.classOf_sourceIdx_eq_targetIdx]
        exact h
      simp [pθ, hrs, hrt]
  intro c d hc hd
  have hlink : N.Linked c.val d.val := Quotient.exact (hc.trans hd.symm)
  have hh := N.linked_imp_eq_of_edge_const hedgeAll c.val c.property d.val hlink d.property
  simpa [pθ, hc, hd] using hh

end Network
end CRNT


namespace CRNT
namespace Network
open scoped BigOperators
variable {S : Type} [DecidableEq S] [Fintype S]

private lemma complexMap_kineticMap_eq_sum_rv_for_jacobian
    (N : Network S) (κ : N.RateConstants) (v : N.ComplexIdx → ℝ) :
    N.complexMap (N.kineticMap κ v) =
      ∑ r : N.R, (κ.k r * v (N.sourceIdx r)) • N.reactionVector r := by
  funext s
  rw [N.complexMap_apply]
  simp only [N.kineticMap_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  have hexpand : ∀ c : N.ComplexIdx,
      κ.k r * v (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) -
            (if N.sourceIdx r = c then 1 else 0)) * (c.val s : ℝ)
        = κ.k r * v (N.sourceIdx r) *
            ((if N.targetIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ) -
              (if N.sourceIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ)) := by
    intro c
    ring
  simp only [hexpand]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    N.sum_ite_complexMap, N.sum_ite_complexMap]
  rw [N.reactionVector_apply]
  rfl

private lemma jacobian_complexLaplacian_factor
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (v : Concentration S) :
    let p : N.ComplexIdx → ℝ := fun c => ∑ s, (c.val s : ℝ) * (v s / x s)
    let z : N.ComplexIdx → ℝ := fun c => N.complexMonomialVector x c * p c
    N.complexMap (N.kineticMap κ z) = (N.massActionJacobian κ x).mulVec v := by
  dsimp only
  rw [complexMap_kineticMap_eq_sum_rv_for_jacobian]
  rw [N.massActionJacobian_mulVec_logform κ hx v]
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [N.massActionRate_eq]
  simp only [sourceIdx]
  ring

private lemma pairing_zero_of_complexMap_zero
    (N : Network S) {a : N.ComplexIdx → ℝ} {p : N.ComplexIdx → ℝ}
    {μ : S → ℝ} (hp : ∀ c, p c = ∑ s, (c.val s : ℝ) * μ s)
    (hYa : N.complexMap a = 0) :
    ∑ c, a c * p c = 0 := by
  have hrewrite : (∑ c, a c * p c) = ∑ s, μ s * N.complexMap a s := by
    calc
      (∑ c, a c * p c) = ∑ c, ∑ s, a c * ((c.val s : ℝ) * μ s) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [hp c, Finset.mul_sum]
      _ = ∑ s, ∑ c, a c * ((c.val s : ℝ) * μ s) := by
        rw [Finset.sum_comm]
      _ = ∑ s, μ s * N.complexMap a s := by
        apply Finset.sum_congr rfl
        intro s _
        rw [N.complexMap_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
  rw [hrewrite, hYa]
  simp

private lemma restricted_pairing_zero
    (N : Network S) (κ : N.RateConstants)
    {θ : Quotient N.linkedSetoid} {z : N.ComplexIdx → ℝ} {p : N.ComplexIdx → ℝ}
    {μ : S → ℝ} (hp : ∀ c, p c = ∑ s, (c.val s : ℝ) * μ s)
    (hzmem : N.restrictToClass θ (N.kineticMap κ z) ∈ N.linkageDeficiencySubspace θ) :
    ∑ c, N.kineticMap κ (N.restrictToClass θ z) c * p c = 0 := by
  have hdef : N.restrictToClass θ (N.kineticMap κ z) ∈ N.deficiencySubspace :=
    (Submodule.mem_inf.mp hzmem).1
  have hker : N.restrictToClass θ (N.kineticMap κ z) ∈ LinearMap.ker N.complexMap :=
    (Submodule.mem_inf.mp hdef).1
  have hY : N.complexMap (N.restrictToClass θ (N.kineticMap κ z)) = 0 :=
    LinearMap.mem_ker.mp hker
  rw [N.kineticMap_restrictToClass]
  exact pairing_zero_of_complexMap_zero N hp hY

/-- A stoichiometric tangent vector in the kernel of the mass-action Jacobian at a
positive deficiency-one steady state is zero.  This is the raw ambient-space form used
by `deficiencyOne_jacobianOnStoich_injective`. -/
theorem massActionJacobianCLM_eq_zero_of_mem_stoich_of_deficiencyOne
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (hss : N.IsMassActionSteadyState κ x)
    {v : Concentration S} (hvStoich : v ∈ N.stoichSubspace)
    (hvJ : N.massActionJacobianCLM κ x v = 0) :
    v = 0 := by
  classical
  let μ : S → ℝ := fun s => v s / x s
  let p : N.ComplexIdx → ℝ := fun c => ∑ s, (c.val s : ℝ) * μ s
  let z : N.ComplexIdx → ℝ := fun c => N.complexMonomialVector x c * p c
  have hp : ∀ c, p c = ∑ s, (c.val s : ℝ) * μ s := fun c => rfl
  have hJmat : (N.massActionJacobian κ x).mulVec v = 0 := by
    rw [← N.massActionJacobianCLM_apply κ x v]
    exact hvJ
  have hYz : N.complexMap (N.kineticMap κ z) = 0 := by
    rw [jacobian_complexLaplacian_factor N κ hx v]
    exact hJmat
  have hzmem : N.kineticMap κ z ∈ N.deficiencySubspace := by
    refine Submodule.mem_inf.mpr ⟨?_, N.kineticMap_mem_range_incidenceMap κ z⟩
    exact LinearMap.mem_ker.mpr hYz
  have hxmemGlobal : N.kineticMap κ (N.complexMonomialVector x) ∈ N.deficiencySubspace :=
    N.kineticMap_complexMonomial_mem_deficiencySubspace κ hss
  have hclass : ∀ θ : Quotient N.linkedSetoid,
      ∃ K : ℝ, ∀ c, N.classOf c = θ → p c = K := by
    intro θ
    have hzθmem : N.restrictToClass θ (N.kineticMap κ z) ∈ N.linkageDeficiencySubspace θ :=
      N.restrictToClass_mem_linkageDeficiencySubspace h.conditions hzmem θ
    have hxθmem : N.restrictToClass θ
        (N.kineticMap κ (N.complexMonomialVector x)) ∈ N.linkageDeficiencySubspace θ :=
      N.restrictToClass_mem_linkageDeficiencySubspace h.conditions hxmemGlobal θ
    rcases N.linkageDeficiency_eq_zero_or_one h.conditions θ with hθ0 | hθ1
    · have hbot := N.linkageDeficiencySubspace_eq_bot_of_deficiency_zero hθ0
      have hz0 : N.restrictToClass θ (N.kineticMap κ z) = 0 := by
        rw [hbot] at hzθmem
        exact hzθmem
      have hx0 : N.restrictToClass θ (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
        rw [hbot] at hxθmem
        exact hxθmem
      let u : N.ComplexIdx → ℝ := N.restrictToClass θ (N.complexMonomialVector x)
      have hunn : ∀ c, 0 ≤ u c := by
        intro c
        by_cases hc : N.classOf c = θ
        · simp only [u, N.restrictToClass_apply_of_eq _ hc]
          exact (Complex.massActionMonomial_pos hx c.val).le
        · simp only [u, N.restrictToClass_apply_of_ne _ hc]
          exact le_rfl
      have hupos : ∀ c, N.classOf c = θ → 0 < u c := by
        intro c hc
        simp only [u, N.restrictToClass_apply_of_eq _ hc]
        exact Complex.massActionMonomial_pos hx c.val
      have hAu : N.kineticMap κ u = 0 := by
        simp only [u, N.kineticMap_restrictToClass, hx0]
      have huz : (fun d => u d * p d) = N.restrictToClass θ z := by
        funext c
        by_cases hc : N.classOf c = θ
        · simp only [u, N.restrictToClass_apply_of_eq _ hc]
          rfl
        · simp only [u, N.restrictToClass_apply_of_ne _ hc]
          simp
      have hpair : ∑ c, N.kineticMap κ (fun d => u d * p d) c * p c = 0 := by
        rw [huz]
        rw [N.kineticMap_restrictToClass, hz0]
        simp
      obtain hconst := N.constant_on_class_of_stationary_weight κ hunn hupos hAu hpair
      obtain ⟨c0, hc0⟩ := Quotient.exists_rep θ
      refine ⟨p c0, fun c hc => ?_⟩
      exact hconst c c0 hc hc0
    · obtain ⟨g, hg0, hgY, hgθ, hspan⟩ :=
        N.exists_spanning_linkageDeficiencySubspace_of_deficiency_one h.conditions hθ1
      obtain ⟨cx, hcx⟩ := hspan _ hxθmem
      obtain ⟨cw, hcw⟩ := hspan _ hzθmem
      by_cases hcx0 : cx = 0
      · have hx0 : N.restrictToClass θ
            (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
          rw [← hcx, hcx0, zero_smul]
        let u : N.ComplexIdx → ℝ := N.restrictToClass θ (N.complexMonomialVector x)
        have hunn : ∀ c, 0 ≤ u c := by
          intro c
          by_cases hc : N.classOf c = θ
          · simp only [u, N.restrictToClass_apply_of_eq _ hc]
            exact (Complex.massActionMonomial_pos hx c.val).le
          · simp only [u, N.restrictToClass_apply_of_ne _ hc]
            exact le_rfl
        have hupos : ∀ c, N.classOf c = θ → 0 < u c := by
          intro c hc
          simp only [u, N.restrictToClass_apply_of_eq _ hc]
          exact Complex.massActionMonomial_pos hx c.val
        have hAu : N.kineticMap κ u = 0 := by
          simp only [u, N.kineticMap_restrictToClass, hx0]
        have huz : (fun d => u d * p d) = N.restrictToClass θ z := by
          funext c
          by_cases hc : N.classOf c = θ
          · simp only [u, N.restrictToClass_apply_of_eq _ hc]
            rfl
          · simp only [u, N.restrictToClass_apply_of_ne _ hc]
            simp
        have hpair : ∑ c, N.kineticMap κ (fun d => u d * p d) c * p c = 0 := by
          rw [huz]
          exact N.restricted_pairing_zero κ hp hzθmem
        obtain hconst := N.constant_on_class_of_stationary_weight κ hunn hupos hAu hpair
        obtain ⟨c0, hc0⟩ := Quotient.exists_rep θ
        refine ⟨p c0, fun c hc => ?_⟩
        exact hconst c c0 hc hc0
      · obtain ⟨σ, ⟨hσθ, hσterm⟩, hσuniq⟩ := h.oneTerminal θ
        obtain ⟨c0, hc0σ⟩ := Quotient.exists_rep σ
        have hc0term : N.IsTerminalSLC c0.val := by
          rw [← isTerminalSLClass_mk, hc0σ]
          exact hσterm
        have hc0θ : N.classOf c0 = θ := by
          have hcl : N.classOf c0 =
              N.strongToLinkage (Quotient.mk N.stronglyLinkedSetoid c0) :=
            (N.strongToLinkage_mk c0).symm
          rw [hcl, hc0σ]
          exact hσθ
        have hSLθ : ∀ c, N.classOf c = θ → N.IsTerminalSLC c.val →
            N.StronglyLinked c0.val c.val := by
          intro c hcθ hcterm
          have e1 : Quotient.mk N.stronglyLinkedSetoid c = σ :=
            hσuniq _ ⟨by rw [strongToLinkage_mk]; exact hcθ,
              by rw [isTerminalSLClass_mk]; exact hcterm⟩
          exact Quotient.exact (hc0σ.trans e1.symm)
        have hwval : ∀ c, N.classOf c = θ →
            z c = N.complexMonomialVector x c * p c := by
          intro c _
          rfl
        have hgp : ∑ c, g c * p c = 0 :=
          pairing_zero_of_complexMap_zero N hp hgY
        exact N.pairing_constant_of_restrictedKineticImage_tangent κ hx
          hc0term hc0θ hSLθ hg0 hgY hgθ hcx0 hcx.symm hwval hcw.symm hgp
  have hpedge : ∀ r : N.R, p (N.targetIdx r) = p (N.sourceIdx r) := by
    intro r
    obtain ⟨K, hK⟩ := hclass (N.classOf (N.sourceIdx r))
    have hs := hK (N.sourceIdx r) rfl
    have htclass : N.classOf (N.targetIdx r) = N.classOf (N.sourceIdx r) := by
      exact (N.classOf_sourceIdx_eq_targetIdx r).symm
    have ht := hK (N.targetIdx r) htclass
    exact ht.trans hs.symm
  have hμorth : μ ∈ orthSum N.stoichSubspace := by
    rw [Network.stoichSubspace]
    apply mem_orthSum_span
    intro g hg
    rcases hg with ⟨r, rfl⟩
    have he := hpedge r
    simp only [p, N.reactionVector_apply, mul_sub] at he ⊢
    rw [Finset.sum_sub_distrib]
    have htarget : ∑ s, μ s * ((N.targetIdx r).val s : ℝ) =
        ∑ s, ((N.targetIdx r).val s : ℝ) * μ s := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    have hsource : ∑ s, μ s * ((N.sourceIdx r).val s : ℝ) =
        ∑ s, ((N.sourceIdx r).val s : ℝ) * μ s := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    have hts : (∑ s, μ s * ((N.targetIdx r).val s : ℝ)) =
        ∑ s, μ s * ((N.sourceIdx r).val s : ℝ) := htarget.trans (he.trans hsource.symm)
    simpa [targetIdx, sourceIdx] using sub_eq_zero.mpr hts
  have hdot : ∑ s, μ s * v s = 0 :=
    (mem_orthSum.mp hμorth) v hvStoich
  have hnonneg : ∀ s : S, 0 ≤ μ s * v s := by
    intro s
    dsimp [μ]
    have hxs := hx s
    have hx0 : 0 ≤ x s := hxs.le
    have hsquare : 0 ≤ v s * v s := mul_self_nonneg _
    rw [div_mul_eq_mul_div]
    exact div_nonneg hsquare hx0
  have hterm : ∀ s : S, μ s * v s = 0 := by
    intro s
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun q (_ : q ∈ (Finset.univ : Finset S)) => hnonneg q)).mp hdot s (Finset.mem_univ s)
  funext s
  have hs := hterm s
  dsimp [μ] at hs
  have hx0 : x s ≠ 0 := (hx s).ne'
  field_simp [hx0] at hs
  have hsq : v s ^ 2 = 0 := by simpa using hs
  exact sq_eq_zero_iff.mp hsq

end Network
end CRNT
