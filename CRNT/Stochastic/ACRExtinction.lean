import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.SignedDrainage
import CRNT.Theorems.DeficiencyZero.PositiveKernel
import CRNT.Stochastic.Kernel
import CRNT.Dynamics.KineticMapPairing

/-!
# Extinction in stochastic networks with absolute concentration robustness

Anderson–Enciso–Johnston ("Stochastic analysis of biochemical reaction networks with absolute
concentration robustness", J. R. Soc. Interface 11, 2014, Theorem 2 = supplementary Theorem 5):
let a network be conservative, of deficiency one, with a positive mass-action steady state for
some rate constants, and with two distinct non-terminal complexes `y₁ ≪ y₂` (`y₂ ≤ y₁`
componentwise; for instance two non-terminal complexes differing in one species, the
Shinar–Feinberg condition). Then for every stoichiometrically admissible kinetics, all
non-terminal complexes are turned off at every positive recurrent state of the stochastic model.

The conclusion depends only on which jumps are possible (a reaction can fire at the count `n`
iff its source fits in `n`, `CanFire`), not on the propensities. On a conservative network every
reachable set is finite, and the positive recurrent states of a finite continuous-time Markov chain
are the states of its closed communicating classes. This module states and proves the theorem in
that form: a count `n` is *recurrent* (`IsRecurrentVia`) when every count reachable from `n`
reaches `n` back.

The proof follows the paper's, with the stationary distribution of the reduced chain replaced by a
positive kernel vector of an auxiliary weakly reversible network whose complexes are the states of
a closed class (`weaklyReversible_exists_positive_kernelVector`); no law of large numbers or
ergodic theorem is needed.

* `CanFire`, `canFire_iff_stochasticMassActionRate_pos`: a reaction can fire iff its stochastic
  mass-action propensity is positive.
* `exists_recurrent_reachable`: on a conservative network, every count reaches a recurrent count.
* `eq_zero_on_nonterminal_of_ker`: for deficiency one with a positive steady state, an element of
  `ker (Y A_κ)` vanishing at one non-terminal complex vanishes at all of them (supplementary
  Theorem 5, assumption 2 of Theorem 4).
* `KernelSupportCondition`, `acrExtinction_general`: supplementary Theorem 4 (any deficiency).
* `kernelSupportCondition_of_deficiencyOne`, `acrExtinction`: supplementary Theorem 5.
* `acrExtinction_reachable`: from every count, the model reaches a recurrent count at which all
  non-terminal complexes are off.
-/

namespace CRNT

namespace Network

open Finset

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The jump graph on counts -/

/-- A complex is **on** at the count `n` when it fits in `n`. -/
def IsOn (y : Complex S) (n : S → ℕ) : Prop := ∀ s, y s ≤ n s

instance (y : Complex S) (n : S → ℕ) : Decidable (IsOn y n) :=
  Fintype.decidableForallFintype

/-- Reaction `r` can fire at the count `n`. -/
def CanFire (N : Network S) (n : S → ℕ) (r : N.R) : Prop := IsOn (N.reaction r).source n

instance (N : Network S) (n : S → ℕ) (r : N.R) : Decidable (N.CanFire n r) :=
  inferInstanceAs (Decidable (IsOn _ _))

/-- **Firing is positive propensity.** -/
theorem canFire_iff_stochasticMassActionRate_pos (N : Network S) (κ : RateConstants N)
    (n : S → ℕ) (r : N.R) : N.CanFire n r ↔ 0 < N.stochasticMassActionRate κ n r := by
  unfold CanFire IsOn stochasticMassActionRate
  constructor
  · intro h
    refine mul_pos (κ.positive r) (Finset.prod_pos fun s _ => ?_)
    exact_mod_cast Nat.descFactorial_pos.mpr (h s)
  · intro h s
    have hprod : 0 < ∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ) :=
      (pos_iff_pos_of_mul_pos h).mp (κ.positive r)
    by_contra hlt
    push Not at hlt
    have h0 : ((n s).descFactorial ((N.reaction r).source s) : ℝ) = 0 := by
      exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hlt
    exact hprod.ne' (Finset.prod_eq_zero (Finset.mem_univ s) h0)

/-- One jump using a reaction satisfying `P`. -/
def JumpStepVia (N : Network S) (P : N.R → Prop) (n m : S → ℕ) : Prop :=
  ∃ r, P r ∧ N.CanFire n r ∧ m = N.jumpNextCount n r

/-- Reachability by jumps using reactions satisfying `P`. -/
def ReachVia (N : Network S) (P : N.R → Prop) : (S → ℕ) → (S → ℕ) → Prop :=
  Relation.ReflTransGen (N.JumpStepVia P)

/-- `n` is **recurrent** for the jumps through `P`: every count reachable from `n` reaches `n`
back (`n` lies in a closed communicating class). -/
def IsRecurrentVia (N : Network S) (P : N.R → Prop) (n : S → ℕ) : Prop :=
  ∀ m, N.ReachVia P n m → N.ReachVia P m n

theorem jumpNextCount_cast (N : Network S) {n : S → ℕ} {r : N.R} (h : N.CanFire n r) (s : S) :
    ((N.jumpNextCount n r s : ℕ) : ℝ) = n s + N.reactionVector r s := by
  simp only [jumpNextCount, reactionVector_apply]
  have := h s
  push_cast [Nat.cast_sub this]
  ring

theorem ReachVia.mono (N : Network S) {P Q : N.R → Prop} (hPQ : ∀ r, P r → Q r)
    {n m : S → ℕ} (h : N.ReachVia P n m) : N.ReachVia Q n m := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨r, hr, hf, rfl⟩ := hstep
    exact ih.tail ⟨r, hPQ r hr, hf, rfl⟩

/-! ## Conservation gives finite reachable sets -/

section Conservative

variable (N : Network S) (w : S → ℝ) (hw : ∀ s, 0 < w s)
  (hcons : ∀ r, ∑ s, w s * N.reactionVector r s = 0)

include hcons in
theorem weight_reachVia {P : N.R → Prop} {n m : S → ℕ} (h : N.ReachVia P n m) :
    ∑ s, w s * (m s : ℝ) = ∑ s, w s * (n s : ℝ) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨r, -, hf, rfl⟩ := hstep
    rw [← ih]
    simp only [jumpNextCount_cast N hf, mul_add, Finset.sum_add_distrib, hcons r, add_zero]

/-- The box of counts with each coordinate at most the conserved weight divided by its weight. -/
noncomputable def weightBox (n : S → ℕ) : Finset (S → ℕ) :=
  Fintype.piFinset fun s => Finset.range (⌈(∑ t, w t * (n t : ℝ)) / w s⌉₊ + 1)

include hw hcons in
theorem mem_weightBox_of_reachVia {P : N.R → Prop} {n m : S → ℕ} (h : N.ReachVia P n m) :
    m ∈ weightBox w n := by
  rw [weightBox, Fintype.mem_piFinset]
  intro s
  rw [Finset.mem_range, Nat.lt_succ_iff]
  have hle : w s * (m s : ℝ) ≤ ∑ t, w t * (m t : ℝ) :=
    Finset.single_le_sum (f := fun t => w t * (m t : ℝ))
      (fun t _ => mul_nonneg (hw t).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
  rw [weight_reachVia N w hcons h] at hle
  have hms : (m s : ℝ) ≤ (∑ t, w t * (n t : ℝ)) / w s := by
    rw [le_div_iff₀ (hw s)]; linarith
  exact_mod_cast hms.trans (Nat.le_ceil _)

/-- The finite set of counts reachable from `n` through `P`. -/
noncomputable def reachFin (P : N.R → Prop) (n : S → ℕ) : Finset (S → ℕ) := by
  classical
  exact (weightBox w n).filter (N.ReachVia P n)

include hw hcons in
theorem mem_reachFin {P : N.R → Prop} {n m : S → ℕ} :
    m ∈ reachFin N w P n ↔ N.ReachVia P n m := by
  classical
  unfold reachFin
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_weightBox_of_reachVia N w hw hcons h, h⟩⟩

include hw hcons in
/-- **Every count reaches a recurrent count** (conservative networks). -/
theorem exists_recurrent_reachable (P : N.R → Prop) (n : S → ℕ) :
    ∃ x, N.ReachVia P n x ∧ N.IsRecurrentVia P x := by
  classical
  have hne : (reachFin N w P n).Nonempty :=
    ⟨n, (mem_reachFin N w hw hcons).mpr Relation.ReflTransGen.refl⟩
  obtain ⟨x, hx, hmin⟩ := (reachFin N w P n).exists_min_image
    (fun x => (reachFin N w P x).card) hne
  have hnx := (mem_reachFin N w hw hcons).mp hx
  refine ⟨x, hnx, fun m hxm => ?_⟩
  have hsub : reachFin N w P m ⊆ reachFin N w P x := fun z hz =>
    (mem_reachFin N w hw hcons).mpr (hxm.trans ((mem_reachFin N w hw hcons).mp hz))
  have hcard := hmin m ((mem_reachFin N w hw hcons).mpr (hnx.trans hxm))
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : x ∈ reachFin N w P m := by
    rw [heq]; exact (mem_reachFin N w hw hcons).mpr Relation.ReflTransGen.refl
  exact (mem_reachFin N w hw hcons).mp this

end Conservative

/-! ## Deficiency one: kernel vectors vanish on all non-terminal complexes or none -/

/-- **Kernel support at deficiency one** (Anderson–Enciso–Johnston, proof of supplementary
Theorem 5). If the network has deficiency one and a positive steady state at `κ`, every `Ψ` with
`Y A_κ Ψ = 0` vanishing at one non-terminal complex vanishes at every non-terminal complex. -/
theorem eq_zero_on_nonterminal_of_ker (N : Network S) (hδ : N.DeficiencyOne)
    (κ : RateConstants N) {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x) {Ψ : N.ComplexIdx → ℝ}
    (hΨ : N.complexMap (N.kineticMap κ Ψ) = 0) {c₁ : N.ComplexIdx}
    (hc₁ : ¬ N.IsTerminalSLC c₁.val) (h0 : Ψ c₁ = 0) :
    ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → Ψ c = 0 := by
  obtain ⟨g, -, hg0, hspan⟩ := N.exists_spanning_deficiencySubspace_of_deficiencyOne hδ
  have hmemΨ : N.kineticMap κ Ψ ∈ N.deficiencySubspace :=
    Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hΨ, N.kineticMap_mem_range_incidenceMap κ Ψ⟩
  obtain ⟨a, ha⟩ := hspan _ hmemΨ
  obtain ⟨b, hb⟩ := hspan _ (N.kineticMap_complexMonomial_mem_deficiencySubspace κ hss)
  have hpos : ∀ c : N.ComplexIdx, 0 < N.complexMonomialVector x c := fun c => by
    rw [complexMonomialVector_apply]; exact Complex.massActionMonomial_pos hx _
  have hb0 : b ≠ 0 := by
    intro hbz
    have hker : N.kineticMap κ (N.complexMonomialVector x) = 0 := by
      rw [← hb, hbz, zero_smul]
    exact (hpos c₁).ne' (kineticMap_eq_zero_of_not_terminal N κ hker hc₁)
  set u : N.ComplexIdx → ℝ := b • Ψ - a • N.complexMonomialVector x with hu
  have hker : N.kineticMap κ u = 0 := by
    rw [hu, map_sub, map_smul, map_smul, ← ha, ← hb, smul_smul, smul_smul, mul_comm, sub_self]
  have hu1 := kineticMap_eq_zero_of_not_terminal N κ hker hc₁
  simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero, zero_sub,
    neg_eq_zero] at hu1
  have ha0 : a = 0 := (mul_eq_zero.mp hu1).resolve_right (hpos c₁).ne'
  intro c hc
  have huc := kineticMap_eq_zero_of_not_terminal N κ hker hc
  simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha0, zero_mul, sub_zero] at huc
  exact (mul_eq_zero.mp huc).resolve_left hb0

/-- A non-terminal complex is the source of some reaction. -/
theorem exists_source_of_not_terminal (N : Network S) {c : Complex S}
    (hc : ¬ N.IsTerminalSLC c) : ∃ r : N.R, (N.reaction r).source = c := by
  by_contra hno
  push Not at hno
  apply hc
  intro r hr
  exfalso
  -- nothing is reachable from `c` except `c`
  have hreach : ∀ d, N.Reaches c d → d = c := by
    intro d hd
    induction hd using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hstep _ _ =>
      obtain ⟨r', hr', -⟩ := hstep
      exact absurd hr' (hno r')
  exact hno r (hreach _ hr.1)

/-! ## The auxiliary network of a closed class -/

section Aux

variable (N : Network S) (P : N.R → Prop) [DecidablePred P] (I : Finset (S → ℕ))

/-- Reactions of the auxiliary network: a state of `I` and a reaction through `P` that can fire
there. -/
abbrev AuxR := {p : I × N.R // P p.2 ∧ N.CanFire p.1.val p.2}

/-- The unit complex of a state. -/
def stateComplex (x : I) : Complex I := Pi.single x 1

variable {N P I}

/-- The auxiliary network whose complexes are the states of a class `I` closed under the jumps
through `P`, and whose reactions are those jumps. -/
noncomputable def auxNet (hclosed : ∀ m ∈ I, ∀ r, P r → N.CanFire m r → N.jumpNextCount m r ∈ I) :
    Network I :=
  ⟨AuxR N P I, inferInstance, inferInstance, fun p =>
    ⟨stateComplex I p.1.1, stateComplex I ⟨N.jumpNextCount p.1.1.val p.1.2,
      hclosed _ p.1.1.2 _ p.2.1 p.2.2⟩⟩⟩

omit [DecidableEq S] in
theorem stateComplex_injective : Function.Injective (stateComplex I) := by
  intro x y h
  have := congrFun h x
  simp only [stateComplex, Pi.single_eq_same] at this
  by_contra hxy
  rw [Pi.single_eq_of_ne hxy] at this
  exact one_ne_zero this

variable (hclosed : ∀ m ∈ I, ∀ r, P r → N.CanFire m r → N.jumpNextCount m r ∈ I)

include hclosed in
theorem auxNet_reaches {m m' : S → ℕ} (hm : m ∈ I) (h : N.ReachVia P m m') :
    ∃ hm' : m' ∈ I, (auxNet hclosed).Reaches (stateComplex I ⟨m, hm⟩)
      (stateComplex I ⟨m', hm'⟩) := by
  induction h with
  | refl => exact ⟨hm, Reaches.refl _ _⟩
  | tail _ hstep ih =>
    obtain ⟨hm₁, hreach⟩ := ih
    obtain ⟨r, hr, hf, rfl⟩ := hstep
    refine ⟨hclosed _ hm₁ r hr hf, hreach.tail ?_⟩
    exact ⟨⟨(⟨_, hm₁⟩, r), hr, hf⟩, rfl, rfl⟩

include hclosed in
theorem auxNet_weaklyReversible (hcomm : ∀ m ∈ I, ∀ m' ∈ I, N.ReachVia P m m') :
    (auxNet hclosed).WeaklyReversible := by
  intro p
  obtain ⟨⟨x, r⟩, hr, hf⟩ := p
  have hnext : N.jumpNextCount x.val r ∈ I := hclosed _ x.2 r hr hf
  obtain ⟨hx', hreach⟩ := auxNet_reaches hclosed hnext (hcomm _ hnext _ x.2)
  exact hreach

end Aux

/-! ## The theorem -/

/-- The kernel condition of Anderson–Enciso–Johnston (supplementary Theorem 4, assumption 2):
every `Ψ ∈ ker (Y A_κ)` vanishing on `C*` vanishes at every non-terminal complex. -/
def KernelSupportCondition (N : Network S) (κ : RateConstants N) (Cstar : Complex S → Prop) :
    Prop :=
  ∀ Ψ : N.ComplexIdx → ℝ, N.complexMap (N.kineticMap κ Ψ) = 0 →
    (∀ c : N.ComplexIdx, Cstar c.val → Ψ c = 0) →
      ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → Ψ c = 0

/-- **Extinction in a closed class of the reduced chain.** Let `I` be a closed communicating class
for the jumps of the reactions whose source is not in `C*`. Under the kernel condition, no
non-terminal complex outside `C*` is on at any state of `I`. -/
theorem nonterminal_off_of_reducedClass_gen (N : Network S) (κ : RateConstants N)
    (Cstar : Complex S → Prop) [DecidablePred Cstar] (hker : N.KernelSupportCondition κ Cstar)
    (I : Finset (S → ℕ))
    (hclosed : ∀ m ∈ I, ∀ r, ¬ Cstar (N.reaction r).source → N.CanFire m r →
      N.jumpNextCount m r ∈ I)
    (hcomm : ∀ m ∈ I, ∀ m' ∈ I, N.ReachVia (fun r => ¬ Cstar (N.reaction r).source) m m') :
    ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ¬ Cstar c.val → ∀ m ∈ I, ¬ IsOn c.val m := by
  classical
  set P : N.R → Prop := fun r => ¬ Cstar (N.reaction r).source with hP
  set A := auxNet (P := P) hclosed with hA
  have hwr : A.WeaklyReversible := auxNet_weaklyReversible hclosed hcomm
  let κA : A.RateConstants := ⟨fun p => κ.k p.1.2, fun p => κ.positive _⟩
  obtain ⟨b, hbpos, hbker⟩ := PositiveKernel.weaklyReversible_exists_positive_kernelVector A hwr κA
  -- the weight of a state
  let B : I → ℝ := fun x => if h : stateComplex I x ∈ A.complexes then b ⟨_, h⟩ else 0
  have hB0 : ∀ x, 0 ≤ B x := by
    intro x; simp only [B]; split_ifs with h
    · exact (hbpos _).le
    · exact le_rfl
  have hBsrc : ∀ p : A.R, b (A.sourceIdx p) = B p.1.1 := by
    intro p
    have hmem : stateComplex I p.1.1 ∈ A.complexes := A.source_mem_complexes p
    simp only [B, hmem, ↓reduceDIte]
    rfl
  -- the class weight of a complex
  let G : Complex S → ℝ := fun y => ∑ x : I, if IsOn y x.val then B x else 0
  -- stationarity of the linear observables
  have hstat : ∀ s, ∑ r : N.R, (if P r then κ.k r * G (N.reaction r).source *
      N.reactionVector r s else 0) = 0 := by
    intro s
    have hpair := sum_kineticMap_mul A κA b
      (fun c => ∑ x : I, (c.val x : ℝ) * ((x.val s : ℕ) : ℝ))
    rw [hbker] at hpair
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hpair
    have hφ : ∀ x : I, ∑ z : I, ((stateComplex I x z : ℕ) : ℝ) * ((z.val s : ℕ) : ℝ) =
        (x.val s : ℝ) := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp [stateComplex]
      · intro z _ hz; simp [stateComplex, Pi.single_eq_of_ne hz]
      · intro h; exact absurd (Finset.mem_univ x) h
    have hterm : ∀ p : A.R, κA.k p * b (A.sourceIdx p) *
        ((fun c : A.ComplexIdx => ∑ x : I, (c.val x : ℝ) * ((x.val s : ℕ) : ℝ)) (A.targetIdx p) -
          (fun c : A.ComplexIdx => ∑ x : I, (c.val x : ℝ) * ((x.val s : ℕ) : ℝ)) (A.sourceIdx p))
        = κ.k p.1.2 * B p.1.1 * N.reactionVector p.1.2 s := by
      intro p
      rw [hBsrc]
      have hsrc : (A.reaction p).source = stateComplex I p.1.1 := rfl
      have htgt : (A.reaction p).target = stateComplex I
          ⟨N.jumpNextCount p.1.1.val p.1.2, hclosed _ p.1.1.2 _ p.2.1 p.2.2⟩ := rfl
      show κ.k p.1.2 * B p.1.1 * (∑ z : I, (((A.reaction p).target z : ℕ) : ℝ) * ((z.val s : ℕ) : ℝ)
        - ∑ z : I, (((A.reaction p).source z : ℕ) : ℝ) * ((z.val s : ℕ) : ℝ)) = _
      rw [htgt, hsrc, hφ, hφ, jumpNextCount_cast N p.2.2]
      ring
    rw [Finset.sum_congr rfl fun p _ => hterm p] at hpair
    -- regroup the sum over jumps by reaction
    have hregroup : ∑ p : A.R, κ.k p.1.2 * B p.1.1 * N.reactionVector p.1.2 s =
        ∑ r : N.R, (if P r then κ.k r * G (N.reaction r).source * N.reactionVector r s
          else 0) := by
      show ∑ p : AuxR N P I, κ.k p.1.2 * B p.1.1 * N.reactionVector p.1.2 s = _
      rw [← Finset.sum_subtype (univ.filter fun q : I × N.R => P q.2 ∧ N.CanFire q.1.val q.2)
        (by intro q; simp) (fun q => κ.k q.2 * B q.1 * N.reactionVector q.2 s),
        Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : P r
      · simp only [hr, true_and, ↓reduceIte, G, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : IsOn (N.reaction r).source x.val
        · have hx' : N.CanFire x.val r := hx
          simp only [hx, hx', ↓reduceIte]
        · have hx' : ¬ N.CanFire x.val r := hx
          simp only [hx, hx', ↓reduceIte, mul_zero, zero_mul]
      · simp [hr]
    rw [hregroup] at hpair
    exact hpair.symm
  -- the complex-space vector
  let Ψ : N.ComplexIdx → ℝ := fun c => if Cstar c.val then 0 else G c.val
  have hΨker : N.complexMap (N.kineticMap κ Ψ) = 0 := by
    funext s
    rw [complexMap_kineticMap_apply, Pi.zero_apply, ← hstat s]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : P r
    · have hne : ¬ Cstar (N.sourceIdx r).val := hr
      simp only [Ψ, hne, hr, ↓reduceIte]
      rfl
    · have heq : Cstar (N.sourceIdx r).val := not_not.mp hr
      simp [Ψ, heq, hr]
  have hzero := hker Ψ hΨker (fun c hc => by simp [Ψ, hc])
  intro c hc hcy m hm hon
  have hΨc : Ψ c = 0 := hzero c hc
  simp only [Ψ, hcy, ↓reduceIte] at hΨc
  -- but `G c > 0`
  obtain ⟨r, hr⟩ := exists_source_of_not_terminal N hc
  have hPr : P r := by
    show ¬ Cstar (N.reaction r).source
    rw [hr]; exact hcy
  have hfire : N.CanFire m r := by unfold CanFire; rw [hr]; exact hon
  set p : A.R := ⟨(⟨m, hm⟩, r), hPr, hfire⟩
  have hBm : 0 < B ⟨m, hm⟩ := by
    rw [← hBsrc p]; exact hbpos _
  have hG : 0 < G c.val := by
    calc (0 : ℝ) < B ⟨m, hm⟩ := hBm
      _ = if IsOn c.val (⟨m, hm⟩ : I).val then B ⟨m, hm⟩ else 0 := by simp only [hon, ↓reduceIte]
      _ ≤ G c.val := Finset.single_le_sum (f := fun x : I => if IsOn c.val x.val then B x else 0)
          (fun x _ => by split_ifs; exacts [hB0 x, le_rfl]) (Finset.mem_univ _)
  exact hG.ne' hΨc

/-- The deficiency-one case of the kernel condition, with `C* = {y₁}`. -/
theorem kernelSupportCondition_of_deficiencyOne (N : Network S) (hδ : N.DeficiencyOne)
    (κ : RateConstants N) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hss : N.IsMassActionSteadyState κ x₀) (y₁ : N.ComplexIdx)
    (hy₁ : ¬ N.IsTerminalSLC y₁.val) : N.KernelSupportCondition κ (· = y₁.val) :=
  fun _ hΨ h0 => eq_zero_on_nonterminal_of_ker N hδ κ hx₀ hss hΨ hy₁ (h0 y₁ rfl)

/-- **Anderson–Enciso–Johnston, supplementary Theorem 4** (combinatorial form). Let `N` be
conservative, let `C*` be a set of non-terminal complexes such that every complex of `C*` is
dominated (`y' ≤ y`) by a non-terminal complex `y'` outside `C*`, and let the kernel condition hold
for some rate constants. Then every non-terminal complex is off at every recurrent count. -/
theorem acrExtinction_general (N : Network S) (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (hcons : ∀ r, ∑ s, w s * N.reactionVector r s = 0) (κ : RateConstants N)
    (Cstar : Complex S → Prop) [DecidablePred Cstar] (hker : N.KernelSupportCondition κ Cstar)
    (hCnt : ∀ c : Complex S, Cstar c → ¬ N.IsTerminalSLC c)
    (hdom : ∀ c : N.ComplexIdx, Cstar c.val → ¬ N.IsTerminalSLC c.val →
      ∃ c' : N.ComplexIdx, ¬ N.IsTerminalSLC c'.val ∧ ¬ Cstar c'.val ∧ ∀ s, c'.val s ≤ c.val s)
    {n : S → ℕ} (hrec : N.IsRecurrentVia (fun _ => True) n) :
    ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ¬ IsOn c.val n := by
  classical
  set P : N.R → Prop := fun r => ¬ Cstar (N.reaction r).source with hP
  obtain ⟨x, hnx, hxrec⟩ := exists_recurrent_reachable N w hw hcons P n
  set I := reachFin N w P x with hI
  have hmemI : ∀ {m}, m ∈ I ↔ N.ReachVia P x m := mem_reachFin N w hw hcons
  have hclosed : ∀ m ∈ I, ∀ r, P r → N.CanFire m r → N.jumpNextCount m r ∈ I := by
    intro m hm r hr hf
    exact hmemI.mpr ((hmemI.mp hm).tail ⟨r, hr, hf, rfl⟩)
  have hcomm : ∀ m ∈ I, ∀ m' ∈ I, N.ReachVia P m m' := by
    intro m hm m' hm'
    exact (hxrec m (hmemI.mp hm)).trans (hmemI.mp hm')
  have hoff := nonterminal_off_of_reducedClass_gen N κ Cstar hker I hclosed hcomm
  have hoffAll : ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ∀ m ∈ I, ¬ IsOn c.val m := by
    intro c hc m hm hon
    by_cases hcs : Cstar c.val
    · obtain ⟨c', hc', hc's, hle⟩ := hdom c hcs hc
      exact hoff c' hc' hc's m hm (fun s => (hle s).trans (hon s))
    · exact hoff c hc hcs m hm hon
  -- the reactions out of `C*` cannot fire on `I`
  have hnofire : ∀ m ∈ I, ∀ r, Cstar (N.reaction r).source → ¬ N.CanFire m r := fun m hm r hr hf =>
    hoffAll ⟨_, N.source_mem_complexes r⟩ (hCnt _ hr) m hm hf
  -- so `I` is closed under all jumps
  have hclosedAll : ∀ {m m'}, m ∈ I → N.ReachVia (fun _ => True) m m' → m' ∈ I := by
    intro m m' hm h
    induction h with
    | refl => exact hm
    | tail _ hstep ih =>
      obtain ⟨r, -, hf, rfl⟩ := hstep
      refine hclosed _ ih r ?_ hf
      intro hsrc
      exact hnofire _ ih r hsrc hf
  have hxn := hrec x (ReachVia.mono N (fun _ _ => trivial) hnx)
  have hnI : n ∈ I := hclosedAll (hmemI.mpr Relation.ReflTransGen.refl) hxn
  intro c hc
  exact hoffAll c hc n hnI
/-- **Anderson–Enciso–Johnston extinction theorem** (supplementary Theorem 5, combinatorial
form). Let `N` be conservative (weights `w > 0` orthogonal to every reaction vector), of
deficiency one, with a positive steady state `x₀` at some rate constants `κ`, and let `y₁ ≠ y₂` be
non-terminal complexes with `y₁ ≪ y₂` (`y₂ ≤ y₁` componentwise). Then at every recurrent count
`n` (every count reachable from `n` reaches `n` back), every non-terminal complex is off. -/
theorem acrExtinction (N : Network S) (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (hcons : ∀ r, ∑ s, w s * N.reactionVector r s = 0) (hδ : N.DeficiencyOne)
    (κ : RateConstants N) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hss : N.IsMassActionSteadyState κ x₀) (y₁ y₂ : N.ComplexIdx)
    (hy₁ : ¬ N.IsTerminalSLC y₁.val) (hy₂ : ¬ N.IsTerminalSLC y₂.val) (hne : y₁ ≠ y₂)
    (hdom : ∀ s, y₂.val s ≤ y₁.val s) {n : S → ℕ}
    (hrec : N.IsRecurrentVia (fun _ => True) n) :
    ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ¬ IsOn c.val n := by
  classical
  refine acrExtinction_general N w hw hcons κ (· = y₁.val)
    (N.kernelSupportCondition_of_deficiencyOne hδ κ hx₀ hss y₁ hy₁)
    (fun c hc => hc ▸ hy₁) (fun c hc _ => ⟨y₂, hy₂, ?_, ?_⟩) hrec
  · intro h; exact hne (Subtype.ext h.symm)
  · intro s; rw [hc]; exact hdom s

/-- **Absorption.** Under the hypotheses of `acrExtinction`, from every count the stochastic model
can reach a recurrent count, and every non-terminal complex is off there. -/
theorem acrExtinction_reachable (N : Network S) (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (hcons : ∀ r, ∑ s, w s * N.reactionVector r s = 0) (hδ : N.DeficiencyOne)
    (κ : RateConstants N) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hss : N.IsMassActionSteadyState κ x₀) (y₁ y₂ : N.ComplexIdx)
    (hy₁ : ¬ N.IsTerminalSLC y₁.val) (hy₂ : ¬ N.IsTerminalSLC y₂.val) (hne : y₁ ≠ y₂)
    (hdom : ∀ s, y₂.val s ≤ y₁.val s) (n : S → ℕ) :
    ∃ m, N.ReachVia (fun _ => True) n m ∧ N.IsRecurrentVia (fun _ => True) m ∧
      ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ¬ IsOn c.val m := by
  obtain ⟨m, hnm, hrec⟩ := exists_recurrent_reachable N w hw hcons (fun _ => True) n
  exact ⟨m, hnm, hrec, acrExtinction N w hw hcons hδ κ hx₀ hss y₁ y₂ hy₁ hy₂ hne hdom hrec⟩

end Network

end CRNT
