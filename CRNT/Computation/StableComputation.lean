import CRNT.Basic.Network
import Mathlib.Logic.Relation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Stable computation by chemical reaction networks

Discrete (count) semantics of a reaction network: a configuration assigns a molecule count
to each species, a reaction is applicable when every source species is present in sufficient
number, and firing it replaces the source complex by the target complex. Following
Chen–Doty–Soloveichik (*Deterministic function computation with chemical reaction networks*,
Natural Computing 13 (2014)), a network **stably computes** `f` if, from the initial
configuration encoding the input `x`, every reachable configuration can reach an
*output-stable* configuration (one from which the output count can never change again) whose
output count is `f x`.

Main results:
* `CRNT.Computation.outputStable_of_terminal` and
  `CRNT.Computation.exists_terminal_of_decreasing`: terminal configurations are output stable,
  and a strictly decreasing potential forces termination.
* `CRNT.Computation.stablyComputes_of_terminating`: a terminating network stably computes
  whatever value all terminal reachable configurations display.
* Worked computations: `minCRN_stablyComputes` (`X₁ + X₂ → Y` computes `min`),
  `addCRN_stablyComputes` (`X₁ → Y`, `X₂ → Y` computes `+`),
  `scaleCRN_stablyComputes` (`X → k Y` computes `k ·`), and
  `maxCRN_stablyComputes` (the four-reaction network
  `X₁ → Z₁ + Y`, `X₂ → Z₂ + Y`, `Z₁ + Z₂ → K`, `K + Y → ∅` computes `max`, a function whose
  computation must consume output).
-/

namespace CRNT

namespace Computation

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A configuration: a molecule count for each species. -/
abbrev Config (S : Type) := S → ℕ

/-- Reaction `r` is applicable at `c` when `c` contains its source complex. -/
def Applicable (N : Network S) (r : N.R) (c : Config S) : Prop :=
  ∀ s, (N.reaction r).source s ≤ c s

/-- The configuration after firing reaction `r` at `c`. -/
def fire (N : Network S) (r : N.R) (c : Config S) : Config S :=
  fun s => c s - (N.reaction r).source s + (N.reaction r).target s

/-- One reaction step. -/
def Step (N : Network S) (c c' : Config S) : Prop :=
  ∃ r, Applicable N r c ∧ c' = fire N r c

/-- Reachability: the reflexive–transitive closure of `Step`. -/
def Reach (N : Network S) : Config S → Config S → Prop := Relation.ReflTransGen (Step N)

/-- A configuration is terminal when no reaction is applicable. -/
def Terminal (N : Network S) (c : Config S) : Prop := ∀ r, ¬ Applicable N r c

/-- A configuration is output stable for output species `o` when the count of `o` is constant
on everything reachable from it. -/
def OutputStable (N : Network S) (o : S) (c : Config S) : Prop :=
  ∀ c', Reach N c c' → c' o = c o

/-- `N` **stably computes** `f` with input encoding `init` and output species `o`. -/
def StablyComputes {α : Type*} (N : Network S) (init : α → Config S) (o : S) (f : α → ℕ) :
    Prop :=
  ∀ x c, Reach N (init x) c → ∃ c', Reach N c c' ∧ OutputStable N o c' ∧ c' o = f x

theorem reach_eq_of_terminal {N : Network S} {c c' : Config S} (hc : Terminal N c)
    (h : Reach N c c') : c' = c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ _ =>
    obtain ⟨r, hr, _⟩ := hstep
    exact absurd hr (hc r)

/-- Terminal configurations are output stable. -/
theorem outputStable_of_terminal {N : Network S} {c : Config S} (hc : Terminal N c) (o : S) :
    OutputStable N o c := fun c' h => by rw [reach_eq_of_terminal hc h]

/-- **Termination from a potential.** If some natural-number potential strictly decreases
along every step, every configuration reaches a terminal configuration. -/
theorem exists_terminal_of_decreasing (N : Network S) (μ : Config S → ℕ)
    (hμ : ∀ c c', Step N c c' → μ c' < μ c) (c : Config S) :
    ∃ c', Reach N c c' ∧ Terminal N c' := by
  induction h : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : Terminal N c
    · exact ⟨c, Relation.ReflTransGen.refl, ht⟩
    · simp only [Terminal, not_forall, not_not] at ht
      obtain ⟨r, hr⟩ := ht
      have hstep : Step N c (fire N r c) := ⟨r, hr, rfl⟩
      obtain ⟨c', hreach, hterm⟩ := ih _ (h ▸ hμ _ _ hstep) (fire N r c) rfl
      exact ⟨c', Relation.ReflTransGen.head hstep hreach, hterm⟩

/-- **Terminating networks compute their terminal output.** -/
theorem stablyComputes_of_terminating {α : Type*} (N : Network S) (init : α → Config S)
    (o : S) (f : α → ℕ) (μ : Config S → ℕ) (hμ : ∀ c c', Step N c c' → μ c' < μ c)
    (hout : ∀ x c, Reach N (init x) c → Terminal N c → c o = f x) :
    StablyComputes N init o f := by
  intro x c hc
  obtain ⟨c', hcc', hterm⟩ := exists_terminal_of_decreasing N μ hμ c
  exact ⟨c', hcc', outputStable_of_terminal hterm o, hout x c' (hc.trans hcc') hterm⟩

/-- An invariant preserved by every step holds on every reachable configuration. -/
theorem reach_invariant (N : Network S) (P : Config S → Prop)
    (hP : ∀ c c', Step N c c' → P c → P c') {c c' : Config S} (h : Reach N c c')
    (hc : P c) : P c' := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact hP _ _ hstep ih

/-! ## Worked computations -/

/-- A network with reactions indexed by `Fin m`. -/
def finNetwork {m : ℕ} (rxn : Fin m → Reaction S) : Network S :=
  ⟨Fin m, inferInstance, inferInstance, rxn⟩

/-- `X₁ + X₂ → Y` (species `0 = X₁`, `1 = X₂`, `2 = Y`). -/
def minCRN : Network (Fin 3) := finNetwork (fun _ : Fin 1 => ⟨![1, 1, 0], ![0, 0, 1]⟩)

/-- Initial configuration for two inputs and output species `2`. -/
def init₂ (x : ℕ × ℕ) : Config (Fin 3) := ![x.1, x.2, 0]

theorem minCRN_stablyComputes :
    StablyComputes minCRN init₂ 2 (fun x => min x.1 x.2) := by
  refine stablyComputes_of_terminating _ _ _ _ (fun c => c 0 + c 1) ?_ ?_
  · rintro c c' ⟨r, hr, rfl⟩
    have h0 := hr 0; have h1 := hr 1
    fin_cases r
    simp_all [minCRN, finNetwork, fire]
    omega
  · intro x c hc hterm
    have inv := reach_invariant minCRN
      (fun c => c 0 + c 2 = x.1 ∧ c 1 + c 2 = x.2) (by
        rintro c c' ⟨r, hr, rfl⟩ ⟨h1, h2⟩
        have h0 := hr 0; have h1' := hr 1
        fin_cases r
        simp_all [minCRN, finNetwork, fire]
        omega) hc (by simp [init₂])
    have ht := hterm ((0 : Fin 1) : minCRN.R)
    simp only [Applicable, minCRN, finNetwork, not_forall, not_le] at ht
    obtain ⟨s, hs⟩ := ht
    fin_cases s <;> simp at hs <;> omega

/-- `X₁ → Y`, `X₂ → Y`. -/
def addCRN : Network (Fin 3) :=
  finNetwork (fun i : Fin 2 => if i = 0 then ⟨![1, 0, 0], ![0, 0, 1]⟩ else ⟨![0, 1, 0], ![0, 0, 1]⟩)

theorem addCRN_stablyComputes :
    StablyComputes addCRN init₂ 2 (fun x => x.1 + x.2) := by
  refine stablyComputes_of_terminating _ _ _ _ (fun c => c 0 + c 1) ?_ ?_
  · rintro c c' ⟨r, hr, rfl⟩
    have h0 := hr 0; have h1 := hr 1
    fin_cases r <;> simp_all [addCRN, finNetwork, fire] <;> omega
  · intro x c hc hterm
    have inv := reach_invariant addCRN (fun c => c 0 + c 1 + c 2 = x.1 + x.2) (by
        rintro c c' ⟨r, hr, rfl⟩ h
        have h0 := hr 0; have h1' := hr 1
        fin_cases r <;> simp_all [addCRN, finNetwork, fire] <;> omega) hc (by simp [init₂])
    have ht0 := hterm ((0 : Fin 2) : addCRN.R)
    have ht1 := hterm ((1 : Fin 2) : addCRN.R)
    simp only [Applicable, addCRN, finNetwork, not_forall, not_le] at ht0 ht1
    obtain ⟨s, hs⟩ := ht0
    obtain ⟨s', hs'⟩ := ht1
    fin_cases s <;> fin_cases s' <;> simp at hs hs' <;> omega

/-- `X → k Y` (species `0 = X`, `1 = Y`). -/
def scaleCRN (k : ℕ) : Network (Fin 2) := finNetwork (fun _ : Fin 1 => ⟨![1, 0], ![0, k]⟩)

/-- Initial configuration for one input and output species `1`. -/
def init₁ (n : ℕ) : Config (Fin 2) := ![n, 0]

theorem scaleCRN_stablyComputes (k : ℕ) :
    StablyComputes (scaleCRN k) init₁ 1 (fun n => k * n) := by
  refine stablyComputes_of_terminating _ _ _ _ (fun c => c 0) ?_ ?_
  · rintro c c' ⟨r, hr, rfl⟩
    have h0 := hr 0
    fin_cases r
    simp_all [scaleCRN, finNetwork, fire]
    omega
  · intro n c hc hterm
    have inv := reach_invariant (scaleCRN k) (fun c => k * c 0 + c 1 = k * n) (by
        rintro c c' ⟨r, hr, rfl⟩ h
        have h0 := hr 0
        fin_cases r
        simp_all [scaleCRN, finNetwork, fire]
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h0
        rw [hm] at h ⊢
        simp only [Nat.add_sub_cancel_left]
        rw [Nat.mul_add, mul_one] at h
        omega) hc (by simp [init₁])
    have ht := hterm ((0 : Fin 1) : (scaleCRN k).R)
    simp only [Applicable, scaleCRN, finNetwork, not_forall, not_le] at ht
    obtain ⟨s, hs⟩ := ht
    fin_cases s <;> simp at hs
    rw [hs, mul_zero, zero_add] at inv
    exact inv

/-- The `max` network (species `0 = X₁`, `1 = X₂`, `2 = Y`, `3 = Z₁`, `4 = Z₂`, `5 = K`):
`X₁ → Z₁ + Y`, `X₂ → Z₂ + Y`, `Z₁ + Z₂ → K`, `K + Y → ∅`. -/
def maxCRN : Network (Fin 6) :=
  finNetwork (fun i : Fin 4 =>
    match i with
    | 0 => ⟨![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0]⟩
    | 1 => ⟨![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 0]⟩
    | 2 => ⟨![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1]⟩
    | 3 => ⟨![0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 0]⟩)

/-- Initial configuration of the `max` network. -/
def initMax (x : ℕ × ℕ) : Config (Fin 6) := ![x.1, x.2, 0, 0, 0, 0]

theorem maxCRN_stablyComputes :
    StablyComputes maxCRN initMax 2 (fun x => max x.1 x.2) := by
  refine stablyComputes_of_terminating _ _ _ _
    (fun c => 3 * c 0 + 3 * c 1 + c 3 + c 4 + c 5) ?_ ?_
  · rintro c c' ⟨r, hr, rfl⟩
    have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; have h3 := hr 3; have h4 := hr 4
    have h5 := hr 5
    fin_cases r <;> simp_all [maxCRN, finNetwork, fire] <;> omega
  · intro x c hc hterm
    have inv := reach_invariant maxCRN
      (fun c => ((c 0 : ℤ) + c 3) - ((c 1 : ℤ) + c 4) = (x.1 : ℤ) - x.2 ∧
        2 * ((c 2 : ℤ) - c 5) + c 0 + c 1 = (x.1 : ℤ) + x.2 + c 3 + c 4) (by
        rintro c c' ⟨r, hr, rfl⟩ ⟨i1, i2⟩
        have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; have h3 := hr 3
        have h4 := hr 4; have h5 := hr 5
        fin_cases r <;> simp_all [maxCRN, finNetwork, fire] <;> omega) hc (by simp [initMax])
    obtain ⟨i1, i2⟩ := inv
    have t0 := hterm ((0 : Fin 4) : maxCRN.R); have t1 := hterm ((1 : Fin 4) : maxCRN.R)
    have t2 := hterm ((2 : Fin 4) : maxCRN.R); have t3 := hterm ((3 : Fin 4) : maxCRN.R)
    simp only [Applicable, maxCRN, finNetwork, not_forall, not_le] at t0 t1 t2 t3
    obtain ⟨s0, hs0⟩ := t0
    obtain ⟨s1, hs1⟩ := t1
    obtain ⟨s2, hs2⟩ := t2
    obtain ⟨s3, hs3⟩ := t3
    fin_cases s0 <;> simp at hs0 <;> fin_cases s1 <;> simp at hs1 <;>
      fin_cases s2 <;> simp at hs2 <;> fin_cases s3 <;> simp at hs3 <;> omega

/-! ## Output-oblivious networks compute only superadditive functions -/

theorem applicable_add {N : Network S} {r : N.R} {c : Config S} (h : Applicable N r c)
    (d : Config S) : Applicable N r (c + d) := fun s => le_add_right (h s)

theorem fire_add {N : Network S} {r : N.R} {c : Config S} (h : Applicable N r c)
    (d : Config S) : fire N r (c + d) = fire N r c + d := by
  funext s
  simp only [fire, Pi.add_apply]
  have := h s
  omega

theorem step_add {N : Network S} {c c' : Config S} (h : Step N c c') (d : Config S) :
    Step N (c + d) (c' + d) := by
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r, applicable_add hr d, (fire_add hr d).symm⟩

/-- Extra molecules never block a run. -/
theorem reach_add_right {N : Network S} {c c' : Config S} (h : Reach N c c') (d : Config S) :
    Reach N (c + d) (c' + d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (step_add hstep d)

/-- Two runs can be executed side by side. -/
theorem reach_add {N : Network S} {a a' b b' : Config S} (ha : Reach N a a')
    (hb : Reach N b b') : Reach N (a + b) (a' + b') := by
  have h1 := reach_add_right ha b
  have h2 := reach_add_right hb a'
  rw [add_comm b a', add_comm b' a'] at h2
  exact h1.trans h2

/-- A network is **output oblivious** for `o` if no reaction consumes `o`. -/
def OutputOblivious (N : Network S) (o : S) : Prop := ∀ r, (N.reaction r).source o = 0

theorem output_mono_of_oblivious {N : Network S} {o : S} (hob : OutputOblivious N o)
    {c c' : Config S} (h : Reach N c c') : c o ≤ c' o := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    obtain ⟨r, _, rfl⟩ := hstep
    simp only [fire, hob r, Nat.sub_zero]
    omega

/-- **Superadditivity** (Chugg–Condon–Hashemi 2018; Severson–Haley–Doty 2019). An output-
oblivious network with additive input encoding can only stably compute superadditive
functions: `f (x + y) ≥ f x + f y`. -/
theorem superadditive_of_outputOblivious {α : Type*} [Add α] {N : Network S}
    {init : α → Config S} {o : S} {f : α → ℕ} (hob : OutputOblivious N o)
    (hinit : ∀ x y, init (x + y) = init x + init y) (hcomp : StablyComputes N init o f)
    (x y : α) : f x + f y ≤ f (x + y) := by
  obtain ⟨cx, hx, -, hxo⟩ := hcomp x (init x) Relation.ReflTransGen.refl
  obtain ⟨cy, hy, -, hyo⟩ := hcomp y (init y) Relation.ReflTransGen.refl
  have hxy : Reach N (init (x + y)) (cx + cy) := by rw [hinit]; exact reach_add hx hy
  obtain ⟨c, hc, -, hco⟩ := hcomp (x + y) (cx + cy) hxy
  have := output_mono_of_oblivious hob hc
  simp only [Pi.add_apply, hxo, hyo] at this
  omega

/-- **`max` needs to consume output.** No output-oblivious network with an additive input
encoding stably computes `max`. -/
theorem not_stablyComputes_max_of_outputOblivious {N : Network S} {init : ℕ × ℕ → Config S}
    {o : S} (hob : OutputOblivious N o) (hinit : ∀ x y, init (x + y) = init x + init y) :
    ¬ StablyComputes N init o (fun x => max x.1 x.2) := by
  intro hcomp
  have := superadditive_of_outputOblivious hob hinit hcomp (1, 0) (0, 1)
  simp at this

/-- The `max` network does consume its output (reaction `K + Y → ∅`). -/
theorem maxCRN_not_outputOblivious : ¬ OutputOblivious maxCRN 2 := by
  intro h
  have := h ((3 : Fin 4) : maxCRN.R)
  simp [maxCRN, finNetwork] at this

/-- `initMax` is additive. -/
theorem initMax_add (x y : ℕ × ℕ) : initMax (x + y) = initMax x + initMax y := by
  funext s; fin_cases s <;> simp [initMax]

end Computation

end CRNT
