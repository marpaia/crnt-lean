import Mathlib.Tactic.DeriveFintype
import CRNT.Stochastic.BirthDeathExhaustive

set_option backward.isDefEq.respectTransparency false

namespace CRNT
namespace ScratchBirthDeathCounterexample

inductive Species | A | B
  deriving DecidableEq, Fintype, Repr

open Species

def c21 : Complex Species := fun s => match s with | A => 2 | B => 1
def c11 : Complex Species := fun _ => 1
def c12 : Complex Species := fun s => match s with | A => 1 | B => 2

inductive Rxn | birth21 | birth11 | death12
  deriving DecidableEq, Fintype, Repr

open Rxn

def rxn : Rxn → Reaction Species
  | birth21 => { source := 0, target := c21 }
  | birth11 => { source := 0, target := c11 }
  | death12 => { source := c12, target := 0 }

def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

@[simp] theorem reaction_birth21 : N.reaction birth21 = { source := 0, target := c21 } := rfl
@[simp] theorem reaction_birth11 : N.reaction birth11 = { source := 0, target := c11 } := rfl
@[simp] theorem reaction_death12 : N.reaction death12 = { source := c12, target := 0 } := rfl

@[simp] theorem c21_A : c21 A = 2 := rfl
@[simp] theorem c21_B : c21 B = 1 := rfl
@[simp] theorem c11_apply (s : Species) : c11 s = 1 := rfl
@[simp] theorem c12_A : c12 A = 1 := rfl
@[simp] theorem c12_B : c12 B = 2 := rfl

 theorem birthExhaustive : N.BirthExhaustive := by
  intro s
  apply N.birthGenerable_of_zeroSourceReaction (r := birth21) rfl
  cases s <;> norm_num [N, rxn, c21]

 theorem deathExhaustive : N.DeathExhaustive := by
  intro s
  apply N.reverseNetwork.birthGenerable_of_zeroSourceReaction (r := death12) rfl
  change 0 < c12 s
  cases s <;> norm_num [c12]

@[simp] theorem intVec_birth21 : N.integerReactionVector birth21 = fun s => match s with | A => 2 | B => 1 := by
  funext s
  cases s <;> norm_num [Network.integerReactionVector, N, rxn, c21]

@[simp] theorem intVec_birth11 : N.integerReactionVector birth11 = fun _ => 1 := by
  funext s
  cases s <;> norm_num [Network.integerReactionVector, N, rxn, c11]

@[simp] theorem intVec_death12 : N.integerReactionVector death12 = fun s => match s with | A => -1 | B => -2 := by
  funext s
  cases s <;> norm_num [Network.integerReactionVector, N, rxn, c12]

 def eA_Z : Species → ℤ := fun s => match s with | A => 1 | B => 0
 def eB_Z : Species → ℤ := fun s => match s with | A => 0 | B => 1

 theorem eA_mem_lattice : eA_Z ∈ N.integerStoichLattice := by
  have h0 : N.integerReactionVector birth21 ∈ N.integerStoichLattice :=
    Submodule.subset_span ⟨birth21, rfl⟩
  have h1 : N.integerReactionVector birth11 ∈ N.integerStoichLattice :=
    Submodule.subset_span ⟨birth11, rfl⟩
  have hsub := N.integerStoichLattice.sub_mem h0 h1
  convert hsub using 1
  funext s
  cases s <;> norm_num [eA_Z, Network.integerReactionVector, N, rxn, c21, c11]

 theorem eB_mem_lattice : eB_Z ∈ N.integerStoichLattice := by
  have h0 : N.integerReactionVector birth21 ∈ N.integerStoichLattice :=
    Submodule.subset_span ⟨birth21, rfl⟩
  have h1 : N.integerReactionVector birth11 ∈ N.integerStoichLattice :=
    Submodule.subset_span ⟨birth11, rfl⟩
  have hcomb := N.integerStoichLattice.sub_mem (N.integerStoichLattice.smul_mem (2 : ℤ) h1) h0
  convert hcomb using 1
  funext s
  cases s <;> norm_num [eB_Z, Network.integerReactionVector, N, rxn, c21, c11]

 theorem fullIntegerLattice : N.GeneratesFullIntegerLattice := by
  apply top_unique
  intro z _
  have hA := N.integerStoichLattice.smul_mem (z A) eA_mem_lattice
  have hB := N.integerStoichLattice.smul_mem (z B) eB_mem_lattice
  have hsum := N.integerStoichLattice.add_mem hA hB
  convert hsum using 1
  funext s
  cases s <;> simp [eA_Z, eB_Z]

@[simp] theorem realVec_birth21 : N.reactionVector birth21 = fun s => match s with | A => 2 | B => 1 := by
  funext s
  cases s <;> norm_num [Network.reactionVector, Reaction.vector, N, rxn, c21]

@[simp] theorem realVec_birth11 : N.reactionVector birth11 = fun _ => 1 := by
  funext s
  cases s <;> norm_num [Network.reactionVector, Reaction.vector, N, rxn, c11]

 def eA_R : Species → ℝ := fun s => match s with | A => 1 | B => 0
 def eB_R : Species → ℝ := fun s => match s with | A => 0 | B => 1

 theorem eA_mem_stoich : eA_R ∈ N.stoichSubspace := by
  have h0 := N.reactionVector_mem_stoichSubspace birth21
  have h1 := N.reactionVector_mem_stoichSubspace birth11
  have hsub := N.stoichSubspace.sub_mem h0 h1
  convert hsub using 1
  funext s
  cases s <;> norm_num [eA_R, Network.reactionVector, Reaction.vector, N, rxn, c21, c11]

 theorem eB_mem_stoich : eB_R ∈ N.stoichSubspace := by
  have h0 := N.reactionVector_mem_stoichSubspace birth21
  have h1 := N.reactionVector_mem_stoichSubspace birth11
  have hcomb := N.stoichSubspace.sub_mem (N.stoichSubspace.smul_mem (2 : ℝ) h1) h0
  convert hcomb using 1
  funext s
  cases s <;> norm_num [eB_R, Network.reactionVector, Reaction.vector, N, rxn, c21, c11]

 theorem fullStoich : N.stoichSubspace = ⊤ := by
  apply top_unique
  intro z _
  have hA := N.stoichSubspace.smul_mem (z A) eA_mem_stoich
  have hB := N.stoichSubspace.smul_mem (z B) eB_mem_stoich
  have hsum := N.stoichSubspace.add_mem hA hB
  convert hsum using 1
  funext s
  cases s <;> simp [eA_R, eB_R]

 def q : Species → ℤ := fun s => match s with | A => 1 | B => -1

 theorem observable_change_fire {n : Species → ℕ} {r : N.R} (hen : N.Enabled n r) :
    Network.integerObservable q (N.fireCount n r) - Network.integerObservable q n =
      ∑ s : Species, q s * N.integerReactionVector r s := by
  unfold Network.integerObservable
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hs := congrFun (N.countDifference_fireCount hen) s
  simp [Network.countDifference] at hs
  linear_combination (q s) * hs

 theorem qdot_intVec (r : N.R) :
    (∑ s : Species, q s * N.integerReactionVector r s) =
      match r with | birth21 => 1 | birth11 => 0 | death12 => 1 := by
  cases r <;> decide

 theorem observable_step_nondec {n m : Species → ℕ} (h : N.CountStep n m) :
    Network.integerObservable q n ≤ Network.integerObservable q m := by
  rcases h with ⟨r, hen, rfl⟩
  have hchange := observable_change_fire hen
  rw [qdot_intVec r] at hchange
  cases r <;> simp only at hchange <;> omega

 theorem observable_reachable_nondec {n m : Species → ℕ} (h : N.CountReachable n m) :
    Network.integerObservable q n ≤ Network.integerObservable q m := by
  induction h with
  | refl => exact le_rfl
  | tail hreach hstep ih => exact le_trans ih (observable_step_nondec hstep)

 def zeroCount : Species → ℕ := fun _ => 0
 def onlyB : Species → ℕ := fun s => match s with | A => 0 | B => 1

 theorem zero_not_reaches_onlyB : ¬ N.CountReachable zeroCount onlyB := by
  intro h
  have hmono := observable_reachable_nondec h
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  simp [Network.integerObservable, huniv, q, zeroCount, onlyB] at hmono

 theorem not_irreducible : ¬ N.CountLatticeIrreducible := by
  intro h
  exact zero_not_reaches_onlyB (h zeroCount onlyB).1

end ScratchBirthDeathCounterexample
end CRNT
