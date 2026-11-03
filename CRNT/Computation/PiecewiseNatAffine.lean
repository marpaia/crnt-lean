import CRNT.Computation.StableComputation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Finite piecewise natural-affine functions and chemical constructions

`PiecewiseNatAffine` means a finite list of affine expressions with natural
coefficients, selected by Boolean combinations of integer linear inequalities.
The file proves closure properties, affine chemical constructions, and restricted
necessity results under additional computation/encoding hypotheses.

This is not the classical class of functions with semilinear graphs. In
particular `floor(n/2)` is stably computable by `2X → Y` but is outside this
natural-affine class, as checked in `test.SemanticCorrespondence`. There is no
claim here that stable computability is equivalent to `PiecewiseNatAffine`.
A full classical characterization also needs a prescribed input encoding.
-/

namespace CRNT

namespace Computation

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Regions: Boolean combinations of linear inequalities -/

/-- The value of the integer linear functional `a` at the natural vector `x`. -/
def dotZ {d : ℕ} (a : Fin d → ℤ) (x : Fin d → ℕ) : ℤ := ∑ i, a i * (x i : ℤ)

@[simp] theorem dotZ_zero {d : ℕ} (x : Fin d → ℕ) : dotZ (fun _ => 0) x = 0 := by
  simp [dotZ]

/-- A **linear formula** on `ℕ^d`: a Boolean combination of the linear inequalities
`a · x ≤ b` with integer coefficients `a : Fin d → ℤ`, `b : ℤ`.  The sets of points
satisfying a linear formula are finite unions of polyhedra; they are the "linear" fragment
of Presburger arithmetic (no congruences, no quantifiers). -/
inductive LinFormula (d : ℕ) where
  /-- The inequality `a · x ≤ b`. -/
  | le (a : Fin d → ℤ) (b : ℤ) : LinFormula d
  /-- The inequality `a · x ≥ b`. -/
  | ge (a : Fin d → ℤ) (b : ℤ) : LinFormula d
  /-- Negation of a formula. -/
  | not (φ : LinFormula d) : LinFormula d
  /-- Conjunction of two formulas. -/
  | and (φ ψ : LinFormula d) : LinFormula d
  /-- Disjunction of two formulas. -/
  | or (φ ψ : LinFormula d) : LinFormula d
  deriving DecidableEq

/-- A point `x ∈ ℕ^d` **satisfies** a linear formula. -/
def LinFormula.Satisfied : LinFormula d → (Fin d → ℕ) → Prop
  | .le a b, x => dotZ a x ≤ b
  | .ge a b, x => b ≤ dotZ a x
  | .not φ, x => ¬ φ.Satisfied x
  | .and φ ψ, x => φ.Satisfied x ∧ ψ.Satisfied x
  | .or φ ψ, x => φ.Satisfied x ∨ ψ.Satisfied x

/-- The region described by a linear formula. -/
def LinFormula.Region (φ : LinFormula d) : Set (Fin d → ℕ) := {x | φ.Satisfied x}

/-! ## Affine maps -/

/-- An **affine map** `ℕ^d → ℕ`: `x ↦ c + ∑ i, e i * x i` with `c, e i ∈ ℕ`. -/
structure Affine (d : ℕ) where
  /-- The constant term. -/
  const : ℕ
  /-- The coefficients of the linear part. -/
  coeff : Fin d → ℕ
  deriving DecidableEq

namespace Affine

/-- The value of the affine map at `x`. -/
def eval (A : Affine d) (x : Fin d → ℕ) : ℕ := A.const + ∑ i, A.coeff i * x i

@[simp] theorem eval_zero (A : Affine d) : A.eval (fun _ => 0) = A.const := by
  simp [eval]

theorem eval_add (A B : Affine d) (x : Fin d → ℕ) :
    (⟨A.const + B.const, fun i => A.coeff i + B.coeff i⟩ : Affine d).eval x = A.eval x + B.eval x := by
  simp only [eval, Nat.add_mul]
  rw [Finset.sum_add_distrib]
  omega

theorem eval_smul (k : ℕ) (A : Affine d) (x : Fin d → ℕ) :
    (⟨k * A.const, fun i => k * A.coeff i⟩ : Affine d).eval x = k * A.eval x := by
  have hsum : (∑ i, (k * A.coeff i) * x i) = k * (∑ i, A.coeff i * x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_assoc k (A.coeff i) (x i)
  simp only [eval, hsum, Nat.mul_add]

/-- If the difference of the linear parts of `A` and `B` is bounded by the difference of
their constant terms at `x`, then `A x ≤ B x`.  This is the linear condition used to
compare two affine maps on a region. -/
theorem eval_diff_le {A B : Affine d} {x : Fin d → ℕ}
    (h : dotZ (fun i => (A.coeff i : ℤ) - B.coeff i) x ≤ (B.const : ℤ) - A.const) :
    A.eval x ≤ B.eval x := by
  have hsum : (∑ i, ((A.coeff i : ℤ) * (x i : ℤ))) - (∑ i, ((B.coeff i : ℤ) * (x i : ℤ)))
      = ∑ i, (((A.coeff i : ℤ) - (B.coeff i : ℤ)) * (x i : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdot : dotZ (fun i => (A.coeff i : ℤ) - (B.coeff i : ℤ)) x
      = (∑ i, ((A.coeff i : ℤ) * (x i : ℤ))) - (∑ i, ((B.coeff i : ℤ) * (x i : ℤ))) := by
    simp only [dotZ]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hz : (A.const : ℤ) + ∑ i, ((A.coeff i : ℤ) * (x i : ℤ))
      ≤ (B.const : ℤ) + ∑ i, ((B.coeff i : ℤ) * (x i : ℤ)) := by
    rw [hdot] at h
    omega
  have hcastA : ((A.eval x : ℤ)) = (A.const : ℤ) + ∑ i, ((A.coeff i : ℤ) * (x i : ℤ)) := by
    simp [eval, Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
  have hcastB : ((B.eval x : ℤ)) = (B.const : ℤ) + ∑ i, ((B.coeff i : ℤ) * (x i : ℤ)) := by
    simp [eval, Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
  rw [← hcastA, ← hcastB] at hz
  exact Int.ofNat_le.mp hz

/-- The comparison of two affine maps is exactly the corresponding linear condition on
`x`.  This is the linear condition used to compare two affine maps on a region. -/
theorem eval_diff_iff {A B : Affine d} {x : Fin d → ℕ} :
    A.eval x ≤ B.eval x ↔
      dotZ (fun i => (A.coeff i : ℤ) - B.coeff i) x ≤ (B.const : ℤ) - A.const := by
  constructor
  · intro h
    have hz : (A.const : ℤ) + ∑ i, ((A.coeff i : ℤ) * (x i : ℤ))
        ≤ (B.const : ℤ) + ∑ i, ((B.coeff i : ℤ) * (x i : ℤ)) := by
      have hcastA : ((A.eval x : ℤ)) = (A.const : ℤ) + ∑ i, ((A.coeff i : ℤ) * (x i : ℤ)) := by
        simp [eval, Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
      have hcastB : ((B.eval x : ℤ)) = (B.const : ℤ) + ∑ i, ((B.coeff i : ℤ) * (x i : ℤ)) := by
        simp [eval, Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
      rw [← hcastA, ← hcastB]
      exact Nat.cast_le.mpr h
    have hdot : dotZ (fun i => (A.coeff i : ℤ) - (B.coeff i : ℤ)) x
        = (∑ i, ((A.coeff i : ℤ) * (x i : ℤ))) - (∑ i, ((B.coeff i : ℤ) * (x i : ℤ))) := by
      simp only [dotZ]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hdot]
    omega
  · exact eval_diff_le

end Affine

/-! ## PiecewiseNatAffine functions -/

/-- A function `f : ℕ^d → ℕ` is **piecewiseNatAffine** if `ℕ^d` is covered by finitely many
regions (Boolean combinations of linear inequalities) on each of which `f` is a fixed
affine map.  See the module docstring for the discussion of this definition. -/
def PiecewiseNatAffine {d : ℕ} (f : (Fin d → ℕ) → ℕ) : Prop :=
  ∃ pieces : List (LinFormula d × Affine d),
    ∀ x, ∃ p ∈ pieces, p.1.Satisfied x ∧ f x = p.2.eval x

/-- Every affine map is piecewiseNatAffine: the whole space is one region and one affine map. -/
theorem piecewiseNatAffine_of_affine {d : ℕ} (c : ℕ) (e : Fin d → ℕ) :
    PiecewiseNatAffine (fun x => c + ∑ i, e i * x i) := by
  refine ⟨[⟨.le (fun _ => 0) 0, ⟨c, e⟩⟩], fun x => ?_⟩
  exact ⟨⟨.le (fun _ => 0) 0, ⟨c, e⟩⟩, by simp, by simp [LinFormula.Satisfied, dotZ],
    by simp [Affine.eval]⟩

namespace PiecewiseNatAffine

/-- **PiecewiseNatAffine functions are closed under addition.**  The regions of `f + g` are the
intersections of the regions of `f` and of `g`. -/
theorem add {d : ℕ} {f g : (Fin d → ℕ) → ℕ} (hf : PiecewiseNatAffine f) (hg : PiecewiseNatAffine g) :
    PiecewiseNatAffine (fun x => f x + g x) := by
  obtain ⟨pf, hpf⟩ := hf
  obtain ⟨pg, hpg⟩ := hg
  refine ⟨pf.flatMap fun p => pg.map fun q =>
    (p.1.and q.1, ⟨p.2.const + q.2.const, fun i => p.2.coeff i + q.2.coeff i⟩), ?_⟩
  intro x
  obtain ⟨p, hp, hpx, hpv⟩ := hpf x
  obtain ⟨q, hq, hqx, hqv⟩ := hpg x
  refine ⟨(p.1.and q.1, ⟨p.2.const + q.2.const, fun i => p.2.coeff i + q.2.coeff i⟩), ?_, ?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
  · exact ⟨hpx, hqx⟩
  · show f x + g x = _
    rw [hpv, hqv]
    exact (Affine.eval_add p.2 q.2 x).symm

/-- **PiecewiseNatAffine functions are closed under `min`.**  On the intersection of the regions of
`f` and `g` the function `min (f x) (g x)` is affine on each of the two subregions
`f x ≤ g x` and `g x ≤ f x`, both of which are linear conditions. -/
theorem min {d : ℕ} {f g : (Fin d → ℕ) → ℕ} (hf : PiecewiseNatAffine f) (hg : PiecewiseNatAffine g) :
    PiecewiseNatAffine (fun x => Nat.min (f x) (g x)) := by
  obtain ⟨pf, hpf⟩ := hf
  obtain ⟨pg, hpg⟩ := hg
  refine ⟨pf.flatMap fun p => pg.flatMap fun q =>
    [(p.1.and (q.1.and (.le (fun i => (p.2.coeff i : ℤ) - q.2.coeff i)
      ((q.2.const : ℤ) - p.2.const))), p.2),
     (p.1.and (q.1.and (.le (fun i => (q.2.coeff i : ℤ) - p.2.coeff i)
      ((p.2.const : ℤ) - q.2.const))), q.2)], ?_⟩
  intro x
  obtain ⟨p, hp, hpx, hpv⟩ := hpf x
  obtain ⟨q, hq, hqx, hqv⟩ := hpg x
  by_cases h : p.2.eval x ≤ q.2.eval x
  · refine ⟨(p.1.and (q.1.and (.le (fun i => (p.2.coeff i : ℤ) - q.2.coeff i)
      ((q.2.const : ℤ) - p.2.const))), p.2), ?_, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_flatMap.mpr ⟨q, hq, by simp⟩⟩
    · refine ⟨hpx, hqx, ?_⟩
      simp only [LinFormula.Satisfied]
      exact Affine.eval_diff_iff.mp h
    · show Nat.min (f x) (g x) = _
      rw [hpv, hqv]
      exact Nat.min_eq_left h
  · refine ⟨(p.1.and (q.1.and (.le (fun i => (q.2.coeff i : ℤ) - p.2.coeff i)
      ((p.2.const : ℤ) - q.2.const))), q.2), ?_, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_flatMap.mpr ⟨q, hq, by simp⟩⟩
    · refine ⟨hpx, hqx, ?_⟩
      simp only [LinFormula.Satisfied]
      exact Affine.eval_diff_iff.mp (by omega)
    · show Nat.min (f x) (g x) = _
      rw [hpv, hqv]
      exact Nat.min_eq_right (by omega)

/-- **PiecewiseNatAffine functions are closed under scalar multiplication.** -/
theorem smul {d : ℕ} {f : (Fin d → ℕ) → ℕ} (hf : PiecewiseNatAffine f) (k : ℕ) :
    PiecewiseNatAffine (fun x => k * f x) := by
  obtain ⟨pf, hpf⟩ := hf
  refine ⟨pf.map fun p => (p.1, ⟨k * p.2.const, fun i => k * p.2.coeff i⟩), fun x => ?_⟩
  obtain ⟨p, hp, hpx, hpv⟩ := hpf x
  refine ⟨(p.1, ⟨k * p.2.const, fun i => k * p.2.coeff i⟩), ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · exact hpx
  · show k * f x = _
    rw [hpv]
    exact (Affine.eval_smul k p.2 x).symm

end PiecewiseNatAffine

/-! ## A function that is not piecewiseNatAffine -/

/-- The exponential function grows at least quadratically. -/
theorem two_pow_ge_sq : ∀ n : ℕ, 4 ≤ n → n * n ≤ 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    by_cases hn : n = 4
    · norm_num [hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
        ⟨n - 1, (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm⟩
      have hm : 4 ≤ m := by omega
      have hsq : m * m ≤ 2 ^ m := ih m (by omega) hm
      have hlin : 2 * m + 1 ≤ 2 ^ m := by
        have h3 : 3 ≤ m := by omega
        have hsq2 : m * m ≥ 2 * m + 1 := by
          calc m * m = m * m := by ring
            _ ≥ m * 3 := Nat.mul_le_mul_left m h3
            _ = 3 * m := by ring
            _ ≥ 2 * m + 1 := by omega
        omega
      calc (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
        _ ≤ 2 ^ m + 2 * m + 1 := by omega
        _ ≤ 2 ^ m + 2 ^ m := by omega
        _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring

/-- `2 ^ n` exceeds every affine function of `n` once `n` is large enough. -/
theorem exists_lt_two_pow {c d n : ℕ} (h : max 4 (c + d) < n) : c + d * n < 2 ^ n := by
  have hsq : n * n ≤ 2 ^ n := two_pow_ge_sq n (by omega)
  have hdn : d + 1 ≤ n := by omega
  have hmul : d * n + n ≤ n * n := by
    calc d * n + n = (d + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hdn
  have hlin : c + d * n < n * n := by omega
  omega

/-- A bound on an affine map of `ℕ` in terms of its coefficients. -/
private def affineBound1 (A : Affine 1) : ℕ := max 4 (A.const + A.coeff 0) + 1

/-- A bound on a list of affine maps of `ℕ`. -/
private def listBound1 (l : List (LinFormula 1 × Affine 1)) : ℕ :=
  List.foldl (fun acc p => max acc (affineBound1 p.2)) 0 l

/-- The bound of a list is at least the initial accumulator. -/
private theorem foldl_max_init (l : List (LinFormula 1 × Affine 1)) (acc : ℕ) :
    acc ≤ List.foldl (fun a q => max a (affineBound1 q.2)) acc l := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons]
    have h1 : acc ≤ max acc (affineBound1 a.2) := by omega
    have h2 : max acc (affineBound1 a.2)
        ≤ List.foldl (fun a q => max a (affineBound1 q.2)) (max acc (affineBound1 a.2)) t :=
      ih _
    exact h1.trans h2

/-- Every entry of a list is bounded by the bound of the list. -/
private theorem foldl_max_mem (l : List (LinFormula 1 × Affine 1)) (acc : ℕ) :
    ∀ p ∈ l, affineBound1 p.2 ≤ List.foldl (fun a q => max a (affineBound1 q.2)) acc l := by
  induction l generalizing acc with
  | nil => intro p hp; simp at hp
  | cons a t ih =>
    intro p hp
    have hmem : p = a ∨ p ∈ t := by simpa using hp
    rcases hmem with hpa | hpt
    · rw [hpa]
      simp only [List.foldl_cons]
      have h1 : affineBound1 a.2 ≤ max acc (affineBound1 a.2) := by omega
      have h2 : max acc (affineBound1 a.2)
          ≤ List.foldl (fun a q => max a (affineBound1 q.2)) (max acc (affineBound1 a.2)) t :=
        foldl_max_init t _
      exact h1.trans h2
    · have h := ih (max acc (affineBound1 a.2)) p hpt
      simpa only [List.foldl_cons] using h

/-- Every entry of a list is bounded by the bound of the list. -/
private theorem listBound1_mem (l : List (LinFormula 1 × Affine 1))
    (p : LinFormula 1 × Affine 1) (hp : p ∈ l) : affineBound1 p.2 ≤ listBound1 l := by
  have h := foldl_max_mem l 0 p hp
  unfold listBound1 at *
  exact h

/-- **The exponential function is not piecewiseNatAffine.**  A piecewiseNatAffine function agrees with an
affine map on each of finitely many regions, and `2 ^ n` meets any affine map in only
finitely many points; hence finitely many regions cannot cover `ℕ`. -/
theorem not_piecewiseNatAffine_pow2 : ¬ PiecewiseNatAffine (fun v : Fin 1 → ℕ => 2 ^ v 0) := by
  rintro ⟨pieces, hp⟩
  have hlarge : ∀ p ∈ pieces,
      p.2.const + p.2.coeff 0 * (listBound1 pieces + 1) < 2 ^ (listBound1 pieces + 1) := by
    intro p hpm
    have hb := listBound1_mem pieces p hpm
    unfold affineBound1 at hb
    have h2 : max 4 (p.2.const + p.2.coeff 0) < listBound1 pieces + 1 := by omega
    exact exists_lt_two_pow h2
  obtain ⟨p, hpm, _, hpv⟩ := hp (listBound1 pieces + 1)
  have heval : p.2.eval (listBound1 pieces + 1)
      = p.2.const + p.2.coeff 0 * (listBound1 pieces + 1) := by
    simp [Affine.eval]
  have htwo : 2 ^ (listBound1 pieces + 1) = p.2.eval (listBound1 pieces + 1) := by
    simpa using hpv
  rw [htwo, heval] at hlarge
  exact absurd (hlarge p hpm) (lt_irrefl _)

/-! ## Linear invariants of reaction networks -/

/-- The net change of the species counts caused by firing the reaction `r`. -/
def delta (N : Network S) (r : N.R) : S → ℤ :=
  fun s => ((N.reaction r).target s : ℤ) - ((N.reaction r).source s : ℤ)

/-- The weighted sum `∑ s, w s * v s`. -/
def wsum (w : S → ℤ) (v : S → ℤ) : ℤ := ∑ s, w s * v s

/-- The weighted sum of a configuration, `∑ s, w s * c s`. -/
def configSum (w : S → ℤ) (c : Config S) : ℤ := wsum w (fun s => (c s : ℤ))

/-- Firing a reaction adds the reaction's stoichiometric change to the configuration. -/
theorem fire_eq_add_delta (N : Network S) (r : N.R) (c : Config S) (h : Applicable N r c) (s : S) :
    (fire N r c s : ℤ) = (c s : ℤ) + delta N r s := by
  have hs : (N.reaction r).source s ≤ c s := h s
  simp only [fire, delta]
  rw [Nat.cast_add, Nat.cast_sub hs]
  ring

/-- The weighted sum of a configuration changes by the weighted sum of the reaction's
stoichiometric change. -/
theorem configSum_fire (N : Network S) (w : S → ℤ) (r : N.R) (c : Config S) (h : Applicable N r c) :
    configSum w (fire N r c) = configSum w c + wsum w (delta N r) := by
  have hle : ∀ s, (fire N r c s : ℤ) = (c s : ℤ) + delta N r s :=
    fun s => fire_eq_add_delta N r c h s
  simp only [configSum, wsum]
  have h1 : (∑ s, w s * (fire N r c s : ℤ)) = ∑ s, w s * ((c s : ℤ) + delta N r s) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [hle]
  have h2 : (∑ s, w s * ((c s : ℤ) + delta N r s))
      = ∑ s, (w s * (c s : ℤ) + w s * delta N r s) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_add]
  rw [h1, h2, Finset.sum_add_distrib]

/-- **A linear invariant.**  If a weighted sum of the species counts is annihilated by
every reaction of the network, it is constant along every run. -/
theorem configSum_invariant (N : Network S) (w : S → ℤ) (hw : ∀ r, wsum w (delta N r) = 0)
    {c c' : Config S} (h : Reach N c c') : configSum w c' = configSum w c := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨r, hr, rfl⟩ := hstep
    rw [configSum_fire N w r _ hr, hw r]
    simpa using ih

/-- `∑ j, g j * (if j = j₀ then c else 0) = g j₀ * c`. -/
theorem sum_ite_mul_eq {d : ℕ} (g : Fin d → ℤ) (j₀ : Fin d) (c : ℤ) :
    (∑ j, g j * (if j = j₀ then c else 0)) = g j₀ * c := by
  rw [Finset.sum_congr rfl (fun j _ => mul_ite _ _ _ _)]
  simp only [mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/-- The cast of a sum of natural numbers is the sum of the casts. -/
theorem cast_sum_nat' {ι : Type} [Fintype ι] (f : ι → ℕ) :
    ((∑ i, f i) : ℤ) = ∑ i, (f i : ℤ) := by
  simp

/-- The sum of the casts of a natural-valued family is the cast of the sum. -/
theorem cast_sum_nat {ι : Type} [Fintype ι] (f : ι → ℕ) :
    (∑ i, (f i : ℤ)) = ((∑ i, f i) : ℤ) := by
  simp

/-- The sum of the products of two casts is the cast of the sum of the products. -/
theorem cast_sum_mul_nat {ι : Type} [Fintype ι] (f g : ι → ℕ) :
    (∑ i, (f i : ℤ) * (g i : ℤ)) = ((∑ i, f i * g i) : ℤ) := by
  have h1 : (∑ i, (f i : ℤ) * (g i : ℤ)) = ∑ i, ((f i * g i : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.cast_mul (f i) (g i)
  rw [h1]

/-- Adding a natural number to a sum of products of casts. -/
theorem cast_add_sum_mul_nat {ι : Type} [Fintype ι] (a : ℕ) (f g : ι → ℕ) :
    (a : ℤ) + ∑ i, (f i : ℤ) * (g i : ℤ) = (a : ℤ) + ∑ i, ((f i * g i : ℕ) : ℤ) := by
  have h1 : (∑ i, (f i : ℤ) * (g i : ℤ)) = ∑ i, ((f i * g i : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.cast_mul (f i) (g i)
  rw [h1]

/-- The cast of a sum with a natural number added. -/
theorem cast_add_sum' {ι : Type} [Fintype ι] (a : ℕ) (f : ι → ℕ) :
    (a : ℤ) + ((∑ i, f i) : ℤ) = ((a + ∑ i, f i) : ℤ) := by
  simp only [Nat.cast_sum]

/-- Adding a natural number to a sum of products of casts, in the other direction. -/
theorem cast_add_sum_mul_nat'' {ι : Type} [Fintype ι] (a : ℕ) (f g : ι → ℕ) :
    (a : ℤ) + ∑ i, (f i : ℤ) * (g i : ℤ) = ((a + ∑ i, f i * g i) : ℤ) := by
  have h1 : ∑ i, (f i : ℤ) * (g i : ℤ) = ∑ i, ((f i * g i : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.cast_mul (f i) (g i)
  have h2 : ∑ i, ((f i * g i : ℕ) : ℤ) = ((∑ i, f i * g i) : ℤ) :=
    cast_sum_nat' (fun i => f i * g i)
  have h3 : (a : ℤ) + ((∑ i, f i * g i) : ℤ) = ((a + ∑ i, f i * g i) : ℤ) :=
    cast_add_sum' a (fun i => f i * g i)
  rw [h1, h2, h3]

/-! ## Affine functions are stably computable -/

/-- The source complex of the reaction `X_j → m j · Y`: one molecule of `X_j`. -/
def affineSourceInl (k : ℕ) (j : Fin k) : (Fin k ⊕ Fin 2) → ℕ :=
  fun s => if s = Sum.inl j then 1 else 0

/-- The target complex of the reaction `X_j → m j · Y`: `m j` molecules of `Y`. -/
def affineTargetInl (k : ℕ) (j : Fin k) (m : Fin k → ℕ) : (Fin k ⊕ Fin 2) → ℕ :=
  fun s => if s = Sum.inr 0 then m j else 0

/-- The source complex of the reaction `C → a · Y`: one molecule of `C`. -/
def affineSourceInr (k : ℕ) : (Fin k ⊕ Fin 2) → ℕ :=
  fun s => if s = Sum.inr 1 then 1 else 0

/-- The target complex of the reaction `C → a · Y`: `a` molecules of `Y`. -/
def affineTargetInr (k : ℕ) (a : ℕ) : (Fin k ⊕ Fin 2) → ℕ :=
  fun s => if s = Sum.inr 0 then a else 0

@[simp] theorem affineSourceInl_inl (k : ℕ) (j j' : Fin k) :
    affineSourceInl k j (Sum.inl j') = if j' = j then 1 else 0 := by
  by_cases h : j' = j <;> simp [affineSourceInl, h, Sum.inl.injEq]

@[simp] theorem affineSourceInl_inr (k : ℕ) (j : Fin k) (i : Fin 2) :
    affineSourceInl k j (Sum.inr i) = 0 := by
  fin_cases i <;> simp [affineSourceInl]

@[simp] theorem affineTargetInl_inr (k : ℕ) (j : Fin k) (m : Fin k → ℕ) (i : Fin 2) :
    affineTargetInl k j m (Sum.inr i) = if i = 0 then m j else 0 := by
  fin_cases i <;> simp [affineTargetInl]

@[simp] theorem affineTargetInl_inl (k : ℕ) (j j' : Fin k) (m : Fin k → ℕ) :
    affineTargetInl k j m (Sum.inl j') = 0 := by
  simp [affineTargetInl]

@[simp] theorem affineSourceInr_inr (k : ℕ) (i : Fin 2) :
    affineSourceInr k (Sum.inr i) = if i = 1 then 1 else 0 := by
  fin_cases i <;> simp [affineSourceInr]

@[simp] theorem affineSourceInr_inl (k : ℕ) (j : Fin k) :
    affineSourceInr k (Sum.inl j) = 0 := by
  simp [affineSourceInr]

@[simp] theorem affineTargetInr_inr (k : ℕ) (a : ℕ) (i : Fin 2) :
    affineTargetInr k a (Sum.inr i) = if i = 0 then a else 0 := by
  fin_cases i <;> simp [affineTargetInr]

@[simp] theorem affineTargetInr_inl (k : ℕ) (a : ℕ) (j : Fin k) :
    affineTargetInr k a (Sum.inl j) = 0 := by
  simp [affineTargetInr]

/-- The reaction network computing the affine function `x ↦ a + ∑ j, m j * x j`.  The
species are `Fin k ⊕ Fin 2`: `Sum.inl j` is the input species `X_j`, `Sum.inr 0` is the
output species `Y` and `Sum.inr 1` is the species `C` carrying the constant `a`.  The
reactions are `X_j → m j · Y` for every `j` and `C → a · Y`. -/
def affineCRN (k : ℕ) (a : ℕ) (m : Fin k → ℕ) : Network (Fin k ⊕ Fin 2) :=
  ⟨Option (Fin k), inferInstance, inferInstance, fun r =>
    match r with
    | some j => ⟨affineSourceInl k j, affineTargetInl k j m⟩
    | none => ⟨affineSourceInr k, affineTargetInr k a⟩⟩

/-- The initial configuration of `affineCRN`: one molecule of the constant species `C`
and `x j` molecules of the input species `X_j`. -/
def affineInit (k : ℕ) (x : Fin k → ℕ) : Config (Fin k ⊕ Fin 2) :=
  fun s => match s with
    | Sum.inl j => x j
    | Sum.inr 0 => 0
    | Sum.inr 1 => 1

/-- The weight of a species for the invariant of the affine network: the output species
weighs `1`, the constant species weighs `a` and the input species `X_j` weighs `m j`. -/
def affineInvariantWeight (k : ℕ) (a : ℕ) (m : Fin k → ℕ) : (Fin k ⊕ Fin 2) → ℤ :=
  fun s => match s with
    | Sum.inl j => (m j : ℤ)
    | Sum.inr 0 => 1
    | Sum.inr 1 => (a : ℤ)

/-- The weight of a species for the potential of the affine network: every molecule that
still has to be processed weighs `1`. -/
def affinePotentialWeight (k : ℕ) : (Fin k ⊕ Fin 2) → ℤ :=
  fun s => match s with
    | Sum.inl _ => 1
    | Sum.inr 0 => 0
    | Sum.inr 1 => 1

/-- The potential of the affine network: the number of molecules that still have to be
processed (the constant molecule included). -/
def affinePotential (k : ℕ) (c : Config (Fin k ⊕ Fin 2)) : ℕ :=
  c (Sum.inr 1) + ∑ j, c (Sum.inl j)

/-- The reaction `X_j → m j · Y` is applicable exactly when the input species `X_j` still
holds a molecule. -/
theorem affineCRN_applicable_inl (k : ℕ) (a : ℕ) (m : Fin k → ℕ) (j : Fin k)
    (c : Config (Fin k ⊕ Fin 2)) :
    Applicable (affineCRN k a m) (some j) c ↔ 1 ≤ c (Sum.inl j) := by
  constructor
  · intro h
    have hh := h (Sum.inl j)
    simp [affineCRN, affineSourceInl] at hh
    omega
  · intro h s
    cases s with
    | inl j' =>
      by_cases hj : j' = j
      · subst hj
        simp [affineCRN, affineSourceInl]
        exact h
      · simp [hj, affineCRN, affineSourceInl]
    | inr i =>
      simp [affineCRN, affineSourceInl]

/-- The reaction `C → a · Y` is applicable exactly when the constant species `C` still
holds a molecule. -/
theorem affineCRN_applicable_inr (k : ℕ) (a : ℕ) (m : Fin k → ℕ)
    (c : Config (Fin k ⊕ Fin 2)) :
    Applicable (affineCRN k a m) none c ↔ 1 ≤ c (Sum.inr 1) := by
  constructor
  · intro h
    have hh := h (Sum.inr 1)
    simp [affineCRN, affineSourceInr] at hh
    omega
  · intro h s
    cases s with
    | inl j' =>
      simp [affineCRN, affineSourceInr]
    | inr i =>
      by_cases hi : i = 1
      · subst hi
        simp [affineCRN, affineSourceInr]
        exact h
      · simp [hi, affineCRN, affineSourceInr]

/-- At a terminal configuration of the affine network all input species and the constant
species are empty. -/
theorem affineCRN_terminal_zero (k : ℕ) (a : ℕ) (m : Fin k → ℕ) {c : Config (Fin k ⊕ Fin 2)}
    (h : Terminal (affineCRN k a m) c) :
    (∀ j : Fin k, c (Sum.inl j) = 0) ∧ c (Sum.inr 1) = 0 := by
  refine ⟨fun j => ?_, ?_⟩
  · by_contra hc
    have hle : 1 ≤ c (Sum.inl j) := by omega
    exact h (some j) ((affineCRN_applicable_inl k a m j c).mpr hle)
  · by_contra hc
    have hle : 1 ≤ c (Sum.inr 1) := by omega
    exact h none ((affineCRN_applicable_inr k a m c).mpr hle)

/-- The invariant weight is annihilated by every reaction of the affine network. -/
theorem affineCRN_delta_invariant (k : ℕ) (a : ℕ) (m : Fin k → ℕ) (r : Option (Fin k)) :
    wsum (affineInvariantWeight k a m) (delta (affineCRN k a m) r) = 0 := by
  cases r with
  | some j =>
    simp only [wsum, Fintype.sum_sum_type, Fin.sum_univ_two]
    have key : ∀ j' : Fin k, (affineInvariantWeight k a m) (Sum.inl j')
        * delta (affineCRN k a m) (some j) (Sum.inl j')
        = (m j' : ℤ) * (if j' = j then (-1 : ℤ) else 0) := by
      intro j'
      by_cases hj : j' = j <;>
        simp [hj, affineInvariantWeight, delta, affineCRN, affineSourceInl, affineTargetInl]
    have hsum : (∑ j' : Fin k, (affineInvariantWeight k a m) (Sum.inl j')
        * delta (affineCRN k a m) (some j) (Sum.inl j')) = -(m j : ℤ) := by
      rw [Finset.sum_congr rfl (fun j' _ => key j')]
      rw [sum_ite_mul_eq]
      simp
    have key0 : (affineInvariantWeight k a m) (Sum.inr 0)
        * delta (affineCRN k a m) (some j) (Sum.inr 0) = (m j : ℤ) := by
      simp [affineInvariantWeight, delta, affineCRN, affineSourceInl, affineTargetInl]
    have key1 : (affineInvariantWeight k a m) (Sum.inr 1)
        * delta (affineCRN k a m) (some j) (Sum.inr 1) = 0 := by
      simp [affineInvariantWeight, delta, affineCRN, affineSourceInl, affineTargetInl]
    rw [hsum, key0, key1]
    ring
  | none =>
    simp only [wsum, Fintype.sum_sum_type, Fin.sum_univ_two]
    have key : ∀ j' : Fin k, (affineInvariantWeight k a m) (Sum.inl j')
        * delta (affineCRN k a m) none (Sum.inl j') = 0 := by
      intro j'
      simp [affineInvariantWeight, delta, affineCRN, affineSourceInr, affineTargetInr]
    have hsum : (∑ j' : Fin k, (affineInvariantWeight k a m) (Sum.inl j')
        * delta (affineCRN k a m) none (Sum.inl j')) = 0 := by
      rw [Finset.sum_congr rfl (fun j' _ => key j')]
      simp
    have key0 : (affineInvariantWeight k a m) (Sum.inr 0)
        * delta (affineCRN k a m) none (Sum.inr 0) = (a : ℤ) := by
      simp [affineInvariantWeight, delta, affineCRN, affineSourceInr, affineTargetInr]
    have key1 : (affineInvariantWeight k a m) (Sum.inr 1)
        * delta (affineCRN k a m) none (Sum.inr 1) = -(a : ℤ) := by
      simp [affineInvariantWeight, delta, affineCRN, affineSourceInr, affineTargetInr]
    rw [hsum, key0, key1]
    ring

/-- The potential weight decreases by one at every reaction of the affine network. -/
theorem affineCRN_delta_potential (k : ℕ) (a : ℕ) (m : Fin k → ℕ) (r : Option (Fin k)) :
    wsum (affinePotentialWeight k) (delta (affineCRN k a m) r) = -1 := by
  cases r with
  | some j =>
    simp only [wsum, Fintype.sum_sum_type, Fin.sum_univ_two]
    have key : ∀ j' : Fin k, (affinePotentialWeight k) (Sum.inl j')
        * delta (affineCRN k a m) (some j) (Sum.inl j')
        = (1 : ℤ) * (if j' = j then (-1 : ℤ) else 0) := by
      intro j'
      by_cases hj : j' = j <;>
        simp [hj, affinePotentialWeight, delta, affineCRN, affineSourceInl, affineTargetInl]
    have hsum : (∑ j' : Fin k, (affinePotentialWeight k) (Sum.inl j')
        * delta (affineCRN k a m) (some j) (Sum.inl j')) = -1 := by
      rw [Finset.sum_congr rfl (fun j' _ => key j')]
      rw [sum_ite_mul_eq]
      simp
    have key0 : (affinePotentialWeight k) (Sum.inr 0)
        * delta (affineCRN k a m) (some j) (Sum.inr 0) = 0 := by
      simp [affinePotentialWeight, delta, affineCRN, affineSourceInl, affineTargetInl]
    have key1 : (affinePotentialWeight k) (Sum.inr 1)
        * delta (affineCRN k a m) (some j) (Sum.inr 1) = 0 := by
      simp [affinePotentialWeight, delta, affineCRN, affineSourceInl, affineTargetInl]
    rw [hsum, key0, key1]
    ring
  | none =>
    simp only [wsum, Fintype.sum_sum_type, Fin.sum_univ_two]
    have key : ∀ j' : Fin k, (affinePotentialWeight k) (Sum.inl j')
        * delta (affineCRN k a m) none (Sum.inl j') = 0 := by
      intro j'
      simp [affinePotentialWeight, delta, affineCRN, affineSourceInr, affineTargetInr]
    have hsum : (∑ j' : Fin k, (affinePotentialWeight k) (Sum.inl j')
        * delta (affineCRN k a m) none (Sum.inl j')) = 0 := by
      rw [Finset.sum_congr rfl (fun j' _ => key j')]
      simp
    have key0 : (affinePotentialWeight k) (Sum.inr 0)
        * delta (affineCRN k a m) none (Sum.inr 0) = 0 := by
      simp [affinePotentialWeight, delta, affineCRN, affineSourceInr, affineTargetInr]
    have key1 : (affinePotentialWeight k) (Sum.inr 1)
        * delta (affineCRN k a m) none (Sum.inr 1) = -1 := by
      simp [affinePotentialWeight, delta, affineCRN, affineSourceInr, affineTargetInr]
    rw [hsum, key0, key1]
    ring

/-- The potential of the affine network is the weighted sum of the configuration with the
potential weight. -/
theorem configSum_potential (k : ℕ) (c : Config (Fin k ⊕ Fin 2)) :
    configSum (affinePotentialWeight k) c
      = ∑ i, (c (Sum.inl i) : ℤ) + (c (Sum.inr 1) : ℤ) := by
  simp only [configSum, wsum, Fintype.sum_sum_type, Fin.sum_univ_two, affinePotentialWeight,
    one_mul, zero_mul]
  have hconv : (∑ a₁, (c (Sum.inl a₁) : ℤ)) = ∑ i, (c (Sum.inl i) : ℤ) := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [hconv]
  ring

/-- The potential of the affine network, as a natural number, is the cast of the weighted
sum of the configuration with the potential weight. -/
theorem configSum_potential_eq (k : ℕ) (c : Config (Fin k ⊕ Fin 2)) :
    configSum (affinePotentialWeight k) c = ((affinePotential k c) : ℤ) := by
  have h1 : configSum (affinePotentialWeight k) c
      = ∑ i, (c (Sum.inl i) : ℤ) + (c (Sum.inr 1) : ℤ) := configSum_potential k c
  have h2 : ((affinePotential k c) : ℤ) = ∑ i, (c (Sum.inl i) : ℤ) + (c (Sum.inr 1) : ℤ) := by
    simp only [affinePotential, Nat.cast_add, Nat.cast_sum]
    exact add_comm _ _
  rw [h1, h2]

/-- The invariant of the affine network on the initial configuration. -/
theorem configSum_affineInit (k : ℕ) (a : ℕ) (m : Fin k → ℕ) (x : Fin k → ℕ) :
    configSum (affineInvariantWeight k a m) (affineInit k x)
      = (a : ℤ) + ∑ j, (m j : ℤ) * (x j : ℤ) := by
  simp only [configSum, wsum, Fintype.sum_sum_type, Fin.sum_univ_two, affineInvariantWeight,
    affineInit, one_mul]
  have hconv : (∑ a₁, (m a₁ : ℤ) * (x a₁ : ℤ)) = ∑ j, (m j : ℤ) * (x j : ℤ) := by
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [hconv]
  ring

/-- The invariant of the affine network at a terminal configuration. -/
theorem configSum_affineTerminal (k : ℕ) (a : ℕ) (m : Fin k → ℕ) {c : Config (Fin k ⊕ Fin 2)}
    (h : (∀ j : Fin k, c (Sum.inl j) = 0) ∧ c (Sum.inr 1) = 0) :
    configSum (affineInvariantWeight k a m) c = ((c (Sum.inr 0) : ℤ)) := by
  simp only [configSum, wsum, Fintype.sum_sum_type, Fin.sum_univ_two, affineInvariantWeight]
  simp [h.1, h.2]

/-- **Every affine function is stably computable.**  The network `affineCRN k a m` computes
the affine function `x ↦ a + ∑ j, m j * x j`. -/
theorem affineCRN_stablyComputes (k : ℕ) (a : ℕ) (m : Fin k → ℕ) :
    StablyComputes (affineCRN k a m) (affineInit k) (Sum.inr 0)
      (fun x => a + ∑ j, m j * x j) := by
  refine stablyComputes_of_terminating _ _ _ _ (affinePotential k) ?_ ?_
  · rintro c c' ⟨r, hr, rfl⟩
    have hdec := configSum_fire (affineCRN k a m) (affinePotentialWeight k) r c hr
    have h1 := configSum_potential_eq k c
    have h2 := configSum_potential_eq k (fire (affineCRN k a m) r c)
    rw [h1, h2] at hdec
    rw [affineCRN_delta_potential k a m r] at hdec
    have hlt : ((affinePotential k (fire (affineCRN k a m) r c) : ℤ))
        < ((affinePotential k c) : ℤ) := by omega
    exact Int.ofNat_lt.mp hlt
  · intro x c hc hterm
    obtain ⟨hz, hc1⟩ := affineCRN_terminal_zero k a m hterm
    have hinv := configSum_invariant (affineCRN k a m) (affineInvariantWeight k a m)
      (affineCRN_delta_invariant k a m) hc
    rw [configSum_affineTerminal k a m ⟨hz, hc1⟩, configSum_affineInit k a m x] at hinv
    have h2 : (c (Sum.inr 0) : ℤ) = ((a + ∑ j, m j * x j) : ℤ) := by
      rw [hinv]
      exact cast_add_sum_mul_nat'' a m x
    exact Int.ofNat_inj.mp h2

/-! ## Firing sequences -/

namespace Seq

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A list of reactions can be fired one after another from `c`. -/
def CanFire (N : Network S) : List N.R → Config S → Prop
  | [], _ => True
  | r :: σ, c => Applicable N r c ∧ CanFire N σ (fire N r c)

/-- The total change of the output count caused by a list of reactions, as a natural
number (the differences are taken in `ℕ`). -/
def outDelta (N : Network S) (o : S) : List N.R → ℕ
  | [] => 0
  | r :: σ => (N.reaction r).target o - (N.reaction r).source o + outDelta N o σ

/-- The configuration obtained by firing a list of reactions. -/
def run (N : Network S) : List N.R → Config S → Config S
  | [], c => c
  | r :: σ, c => run N σ (fire N r c)

/-- The net stoichiometric change of a list of reactions. -/
def deltaZ (N : Network S) : List N.R → S → ℤ
  | [], _ => 0
  | r :: σ, s => delta N r s + deltaZ N σ s

/-- The configuration reached by a firing sequence differs from the initial one by the
sequence's net stoichiometric change. -/
theorem run_eq_add_deltaZ : ∀ (σ : List N.R) (c : Config S), CanFire N σ c → ∀ s,
    (run N σ c s : ℤ) = (c s : ℤ) + deltaZ N σ s := by
  intro σ
  induction σ with
  | nil => intro c _ s; simp [run, deltaZ]
  | cons r σ ih =>
    intro c hσ s
    have hr := hσ.1
    have hσ' := hσ.2
    have h1 := fire_eq_add_delta N r c hr s
    have h2 := ih (fire N r c) hσ' s
    simp only [run, deltaZ]
    omega

end Seq

/-- **Stable computation pins the output of terminal configurations.**  If a network stably
computes `f`, then every terminal configuration reachable from the initial configuration of
`x` displays the output count `f x`.  (The stable configuration reached from a terminal one
is the terminal configuration itself.) -/
theorem output_of_terminal_reachable {α : Type} {N : Network S} {init : α → Config S}
    {o : S} {f : α → ℕ} (hcomp : StablyComputes N init o f) (x : α) {c : Config S}
    (hc : Reach N (init x) c) (hterm : Terminal N c) : c o = f x := by
  obtain ⟨c', hc', _, hc'o⟩ := hcomp x c hc
  have : c' = c := reach_eq_of_terminal hterm hc'
  rw [← this]
  exact hc'o

/-! ## A uniform computation gives an affine function -/

/-- The natural-number output change of a sequence equals the cast of its net change, if
no reaction decreases the number of output molecules. -/
theorem Seq.outDelta_eq_deltaZ {N : Network S} {o : S} (σ : List N.R)
    (hmono : ∀ r, (N.reaction r).source o ≤ (N.reaction r).target o) :
    (outDelta N o σ : ℤ) = deltaZ N σ o := by
  induction σ with
  | nil => simp [outDelta, deltaZ]
  | cons r σ ih =>
    have h := hmono r
    have h2 := ih
    have h3 : ((N.reaction r).target o : ℤ) - ((N.reaction r).source o : ℤ)
        = (((N.reaction r).target o - (N.reaction r).source o : ℕ) : ℤ) := by
      rw [Nat.cast_sub h]
    have h4 : delta N r o = ((N.reaction r).target o : ℤ) - ((N.reaction r).source o : ℤ) := rfl
    simp only [outDelta, deltaZ]
    rw [Nat.cast_add]
    omega

/-- The net output change of a sequence of reactions is non-negative if no reaction
decreases the number of output molecules. -/
theorem Seq.deltaZ_nonneg {N : Network S} {o : S} (σ : List N.R)
    (hmono : ∀ r, (N.reaction r).source o ≤ (N.reaction r).target o) :
    0 ≤ Seq.deltaZ N σ o := by
  induction σ with
  | nil => simp [Seq.deltaZ]
  | cons r σ ih =>
    simp only [Seq.deltaZ]
    have h := hmono r
    have h2 : 0 ≤ Seq.deltaZ N σ o := ih
    have h3 : 0 ≤ delta N r o := by
      have h4 : (0 : ℤ) ≤ ((N.reaction r).target o : ℤ) - ((N.reaction r).source o : ℤ) := by
        omega
      simpa only [delta] using h4
    omega

/-- **A uniform firing sequence computes an affine function.**  Suppose that *one and the
same* sequence of reactions `σ` can be fired for every input, that the configuration it
leads to is always terminal, and that no reaction decreases the number of output molecules.
Then the computed function is affine (hence piecewiseNatAffine).

This is a special case of the Chen–Doty–Soloveichik necessity direction: the output of a
run is the initial output count plus the net stoichiometric change of the run, and the net
change of a *fixed* sequence is a constant. -/
theorem uniform_computation_affine {k : ℕ} {N : Network S} {init : (Fin k → ℕ) → Config S}
    {o : S} {f : (Fin k → ℕ) → ℕ} {base : Config S} {vec : Fin k → Config S}
    (hinit : ∀ (v : Fin k → ℕ) s, init v s = base s + ∑ j, vec j s * v j)
    (σ : List N.R) (happ : ∀ v, Seq.CanFire N σ (init v))
    (hterm : ∀ v, Terminal N (Seq.run N σ (init v)))
    (hmono : ∀ r, (N.reaction r).source o ≤ (N.reaction r).target o)
    (hcomp : StablyComputes N init o f) :
    PiecewiseNatAffine f := by
  have hnonneg : 0 ≤ Seq.deltaZ N σ o := Seq.deltaZ_nonneg σ hmono
  have hout : ∀ v, (f v : ℤ) = (init v o : ℤ) + (Seq.deltaZ N σ o : ℤ) := by
    intro v
    have hreach : ∀ (σ : List N.R) (c : Config S), Seq.CanFire N σ c → Reach N c (Seq.run N σ c) := by
      -- the sequence can be fired, so the end configuration is reachable
      intro σ
      induction σ with
      | nil => intro c _; exact Relation.ReflTransGen.refl
      | cons r σ ih =>
        intro c hσ
        exact Relation.ReflTransGen.head ⟨r, hσ.1, rfl⟩ (ih (fire N r c) hσ.2)
    have hreach' : Reach N (init v) (Seq.run N σ (init v)) := hreach σ (init v) (happ v)
    have hval := output_of_terminal_reachable hcomp v hreach' (hterm v)
    have hz := Seq.run_eq_add_deltaZ σ (init v) (happ v) o
    rw [hval] at hz
    omega
  refine ⟨[⟨.le (fun _ => 0) 0, ⟨base o + Seq.outDelta N o σ, fun j => vec j o⟩⟩],
    fun v => ?_⟩
  refine ⟨⟨.le (fun _ => 0) 0, ⟨base o + Seq.outDelta N o σ, fun j => vec j o⟩⟩, by simp,
    ?_, ?_⟩
  · simp [LinFormula.Satisfied, dotZ]
  · have hz : (f v : ℤ) = ((init v o + Seq.outDelta N o σ : ℕ) : ℤ) := by
      have h := hout v
      have h3 : (Seq.deltaZ N σ o : ℤ) = (Seq.outDelta N o σ : ℤ) :=
        (Seq.outDelta_eq_deltaZ σ hmono).symm
      rw [h, h3]
      rw [Nat.cast_add]
    have hz2 : f v = init v o + Seq.outDelta N o σ := Int.ofNat_inj.mp hz
    rw [Affine.eval]
    calc f v = init v o + Seq.outDelta N o σ := hz2
      _ = (base o + ∑ j, vec j o * v j) + Seq.outDelta N o σ := by rw [hinit v o]
      _ = base o + Seq.outDelta N o σ + ∑ j, vec j o * v j := by ring

/-! ## The necessity direction for output-conserving networks -/

/-- **Necessity of piecewiseNatAffineity for output-conserving networks.**  Suppose the count of the
output species is conserved by every reaction of the network (no reaction changes the number
of output molecules) and the input encoding is affine.  Then the function computed by the
network is affine, hence piecewiseNatAffine.

This is a special case of the Chen–Doty–Soloveichik necessity direction: a stable
computation cannot change the output count, so the output is *pinned* by the conserved
quantity. -/
theorem output_conserving_affine {k : ℕ} {N : Network S} {init : (Fin k → ℕ) → Config S}
    {o : S} {f : (Fin k → ℕ) → ℕ} {base : Config S} {vec : Fin k → Config S}
    (hinit : ∀ (v : Fin k → ℕ) s, init v s = base s + ∑ j, vec j s * v j)
    (hcons : ∀ r, (N.reaction r).target o = (N.reaction r).source o)
    (hcomp : StablyComputes N init o f) :
    ∀ (v : Fin k → ℕ), f v = base o + ∑ j, vec j o * v j := by
  intro v
  have hinv : ∀ c, Reach N (init v) c → c o = (init v) o := by
    intro c hc
    exact reach_invariant N (fun c => c o = (init v) o)
      (fun c c' hstep h => by
        obtain ⟨r, hr, rfl⟩ := hstep
        simp only [fire]
        have hro := hcons r
        have hle := hr o
        omega) hc (rfl)
  obtain ⟨c', hc', hstable, hc'o⟩ := hcomp v (init v) Relation.ReflTransGen.refl
  have h1 : c' o = (init v) o := hinv c' hc'
  rw [← hc'o, h1]
  have h2 : (init v) o = base o + ∑ j, vec j o * v j := by
    have := hinit v o
    omega
  exact h2

/-- **Output-conserving networks compute piecewiseNatAffine functions.** -/
theorem output_conserving_piecewiseNatAffine {k : ℕ} {N : Network S} {init : (Fin k → ℕ) → Config S}
    {o : S} {f : (Fin k → ℕ) → ℕ} {base : Config S} {vec : Fin k → Config S}
    (hinit : ∀ (v : Fin k → ℕ) s, init v s = base s + ∑ j, vec j s * v j)
    (hcons : ∀ r, (N.reaction r).target o = (N.reaction r).source o)
    (hcomp : StablyComputes N init o f) :
    PiecewiseNatAffine f := by
  have h := output_conserving_affine hinit hcons hcomp
  refine ⟨[⟨.le (fun _ => 0) 0, ⟨base o, fun j => vec j o⟩⟩], fun x => ?_⟩
  refine ⟨⟨.le (fun _ => 0) 0, ⟨base o, fun j => vec j o⟩⟩, by simp, ?_, ?_⟩
  · simp [LinFormula.Satisfied, dotZ]
  · rw [h x]
    simp [Affine.eval]

/-! ## Examples -/

/-- **The minimum of two affine functions is piecewiseNatAffine.**  The two subregions `f ≤ g` and
`g ≤ f` are linear conditions. -/
theorem min_of_affine_piecewiseNatAffine {d : ℕ} (c₁ c₂ : ℕ) (e₁ e₂ : Fin d → ℕ) :
    PiecewiseNatAffine (fun x => Nat.min (c₁ + ∑ i, e₁ i * x i) (c₂ + ∑ i, e₂ i * x i)) :=
  PiecewiseNatAffine.min (piecewiseNatAffine_of_affine c₁ e₁) (piecewiseNatAffine_of_affine c₂ e₂)

/-- `∑ j, (if j = i then 1 else 0) * x j = x i`. -/
theorem sum_eq_single' {d : ℕ} (i : Fin d) (x : Fin d → ℕ) :
    (∑ j : Fin d, (if j = i then 1 else 0) * x j) = x i := by
  calc (∑ j : Fin d, (if j = i then 1 else 0) * x j)
      = ∑ j : Fin d, if j = i then x j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = i <;> simp [h]
    _ = x i := by
      rw [Finset.sum_ite_eq']
      simp

/-- **The function `min (x 0) (x 1)` is piecewiseNatAffine.** -/
theorem min_piecewiseNatAffine : PiecewiseNatAffine (fun x : Fin 2 → ℕ => Nat.min (x 0) (x 1)) := by
  have h := min_of_affine_piecewiseNatAffine 0 0 (fun i : Fin 2 => if i = 0 then 1 else 0)
    (fun i : Fin 2 => if i = 1 then 1 else 0)
  convert h using 1
  funext x
  simp

/-- The function `x ↦ 2 * x` is piecewiseNatAffine (it is affine). -/
theorem two_mul_piecewiseNatAffine : PiecewiseNatAffine (fun x : Fin 1 → ℕ => 2 * x 0) := by
  refine ⟨[⟨.le (fun _ => 0) 0, ⟨0, fun _ => 2⟩⟩], fun x => ?_⟩
  refine ⟨⟨.le (fun _ => 0) 0, ⟨0, fun _ => 2⟩⟩, by simp, ?_, ?_⟩
  · simp [LinFormula.Satisfied, dotZ]
  · simp [Affine.eval]

/-- The function `x ↦ 2 ^ x` is **not** piecewiseNatAffine. -/
theorem pow2_not_piecewiseNatAffine : ¬ PiecewiseNatAffine (fun x : Fin 1 → ℕ => 2 ^ x 0) := not_piecewiseNatAffine_pow2

end Computation



end CRNT
