import CRNT.Decision.DeficiencyOneConditionsDecide
import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Deficiency.DeficiencyOneDecide
import CRNT.Examples.ReversiblePair

/-!
# A decidable test for the deficiency-one hypotheses

Feinberg's deficiency-one theorem (Feinberg, *Chemical reaction network structure and the
stability of complex isothermal reactors—I*, 1979) applies to a network whose three
*structural* hypotheses hold:

1. every linkage class has deficiency at most one (`δ_θ ≤ 1`);
2. the per-class deficiencies sum to the network deficiency (`∑_θ δ_θ = δ`);
3. every linkage class contains exactly one **terminal strong linkage class**.

The repository already decides the two halves separately:

* `CRNT.Decision.DeficiencyOneConditionsDecide` decides conditions (1) and (2) — the bundle
  `N.DeficiencyOneConditions` — by routing both fields through the *computable* per-class
  deficiency `N.computeLinkageDeficiency` and the computable network deficiency
  `N.computableDeficiency`;
* `CRNT.Deficiency.DeficiencyOneDecide` decides condition (3) — `N.OneTerminalSLCPerLinkageClass`
  — by a chain of computable instances over the finite vertex type of the network's complexes.

What was missing is the **bundle**: the whole hypothesis bundle `N.DeficiencyOneHypotheses`
(the structure of `CRNT.Deficiency.DeficiencyOneHypotheses`) carried no `Decidable` instance,
and there was no bridge from the *computable* per-class deficiencies to the propositional
statement used by the deficiency-one theorems of `CRNT/Theorems/DeficiencyOne/`. This module
supplies both:

* `decidableDeficiencyOneHypotheses` — the whole hypothesis bundle is decidable;
* `deficiencyOneHypotheses_iff_compute` — the bundle holds **iff** the fully computable
  per-class deficiencies satisfy the two numerical conditions and the (decidable) terminal
  linkage condition holds.

## Kernel `decide` versus compiled `#eval`

The decision is *not* kernel-`decide`-reducible. The per-class deficiency is computed as
`computeLinkageDeficiency`, whose class rank is `computeRank` of the class's rational
stoichiometric matrix — a determinant over a permutation sum — and the kernel does not reduce
it: `by decide` on `N.DeficiencyOneHypotheses` gets stuck at the reduction of
`N.computeLinkageDeficiency`. The *terminal-linkage half*, by contrast, **is**
kernel-`decide`-reducible (`instDecidableOneTerminalSLCPerLinkageClass`, exercised by
`example : N.OneTerminalSLCPerLinkageClass := by decide` in
`CRNT/Deficiency/DeficiencyOneDecide.lean`). Concrete decisions are therefore obtained by
*compiled* evaluation (`#eval`), not by `decide`; the example below evaluates the whole bundle
to `true` on a genuine deficiency-one network.

## Scope: the hypotheses only

This is a decision procedure for the *structural hypotheses* of the deficiency-one theorem. It
is **not** a decision procedure for the *semantic* feasibility test `N.DOAFeasible` of
`CRNT.Multistationarity.DeficiencyOneAlgorithm`, which is a statement over `ℝ` (the existence
of a candidate flux with a sign-compatible capacity) and has **no** `Decidable` instance and
no numerical/LP procedure. Nor does it settle the two-shelf/multi-shelf decomposition of a
capacity flux, which remains open: `CRNT.Network.twoShelf_cannot_iterate` (a pairing-constant
shelf cannot be split into two parts) and `CRNT.Network.threeShelf_freedom` (the two global
balances supply only two moments) show that the two-value argument does not iterate.

Depends on: `CRNT.Decision.DeficiencyOneConditionsDecide`,
`CRNT.Deficiency.DeficiencyOneHypotheses`, `CRNT.Deficiency.DeficiencyOneDecide`,
`CRNT.Examples.ReversiblePair`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Any two `Fintype` instances on the linkage-class quotient enumerate the same classes.**
The ambient (noncomputable) instance `instFintypeQuotientLinked` of
`CRNT.Deficiency.LinkageDeficiency` and the computable instance
`instFintypeQuotientLinkageClass` of `CRNT.Deficiency.DeficiencyOneDecide` therefore have the
same `Finset.univ`. -/
theorem finset_univ_linkageClass_eq (N : Network S)
    (i j : Fintype (Quotient N.linkedSetoid)) :
    @Finset.univ (Quotient N.linkedSetoid) i = @Finset.univ (Quotient N.linkedSetoid) j :=
  congrArg (@Finset.univ (Quotient N.linkedSetoid)) (Subsingleton.elim i j)

/-- **Summing over the linkage classes does not depend on the `Fintype` instance used.** -/
theorem sum_linkageClass_eq_of_fintype (N : Network S)
    (i j : Fintype (Quotient N.linkedSetoid)) (f : Quotient N.linkedSetoid → ℤ) :
    Finset.sum (@Finset.univ (Quotient N.linkedSetoid) i) f
      = Finset.sum (@Finset.univ (Quotient N.linkedSetoid) j) f :=
  Finset.sum_congr (finset_univ_linkageClass_eq N i j) (fun _ _ => rfl)

/-- **The hypothesis bundle is the conjunction of its two fields.** The structure
`N.DeficiencyOneHypotheses` of `CRNT.Deficiency.DeficiencyOneHypotheses` bundles the two
decidable conditions (i)–(ii) and (iii). -/
theorem deficiencyOneHypotheses_iff (N : Network S) :
    N.DeficiencyOneHypotheses ↔ N.DeficiencyOneConditions ∧ N.OneTerminalSLCPerLinkageClass := by
  constructor
  · intro h; exact ⟨h.conditions, h.oneTerminal⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

/-- **The deficiency-one hypotheses are decidable.** The three structural conditions of
Feinberg's deficiency-one theorem — (i) each linkage class has deficiency at most one, (ii) the
class deficiencies sum to the network deficiency, (iii) each linkage class has exactly one
terminal strong linkage class — are all decidable, so the *whole* hypothesis bundle is
decidable and can be tested by compiled evaluation. -/
instance decidableDeficiencyOneHypotheses (N : Network S) :
    Decidable N.DeficiencyOneHypotheses :=
  decidable_of_iff (N.DeficiencyOneConditions ∧ N.OneTerminalSLCPerLinkageClass)
    (deficiencyOneHypotheses_iff N).symm

/-- **The computable deficiency-one test is equivalent to the propositional hypothesis bundle.**
The hypothesis bundle holds if and only if the *fully computable* per-class deficiencies satisfy
the two numerical conditions and the (decidable) terminal-linkage condition holds. The sum
ranges over the linkage classes through the computable `Fintype` instance
`instFintypeQuotientLinkageClass` (the one the plain `∑` notation elaborates to here). -/
theorem deficiencyOneHypotheses_iff_compute (N : Network S) :
    N.DeficiencyOneHypotheses ↔
      (∀ q, N.computeLinkageDeficiency q ≤ 1) ∧
        (∑ q, N.computeLinkageDeficiency q = (N.computableDeficiency : ℤ)) ∧
        N.OneTerminalSLCPerLinkageClass := by
  constructor
  · intro h
    refine ⟨?_, ?_, h.oneTerminal⟩
    · intro q
      rw [← N.linkageDeficiency_eq_computeLinkageDeficiency q]
      exact h.conditions.linkageDeficiency_le_one q
    · have h2 : Finset.sum (@Finset.univ (Quotient N.linkedSetoid) (instFintypeQuotientLinked N))
          (fun q => N.linkageDeficiency q) = N.deficiencyInt := h.conditions.sum_eq
      have h3 : Finset.sum (@Finset.univ (Quotient N.linkedSetoid) (instFintypeQuotientLinkageClass N))
          (fun q => N.linkageDeficiency q) = N.deficiencyInt :=
        (sum_linkageClass_eq_of_fintype N (instFintypeQuotientLinked N)
          (instFintypeQuotientLinkageClass N) (fun q => N.linkageDeficiency q)).symm.trans h2
      have h4 := (N.sum_linkageDeficiency_eq_deficiencyInt_iff_compute).mp h3
      exact h4
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_⟩, h3⟩
    · intro q
      rw [N.linkageDeficiency_eq_computeLinkageDeficiency q]
      exact h1 q
    · have h2' : Finset.sum (@Finset.univ (Quotient N.linkedSetoid) (instFintypeQuotientLinkageClass N))
          (fun q => N.computeLinkageDeficiency q) = (N.computableDeficiency : ℤ) := h2
      have h2'' : Finset.sum (@Finset.univ (Quotient N.linkedSetoid) (instFintypeQuotientLinkageClass N))
          (fun q => N.linkageDeficiency q) = N.deficiencyInt :=
        (N.sum_linkageDeficiency_eq_deficiencyInt_iff_compute).mpr h2'
      exact (sum_linkageClass_eq_of_fintype N (instFintypeQuotientLinked N)
        (instFintypeQuotientLinkageClass N) (fun q => N.linkageDeficiency q)).trans h2''

end Network

end CRNT

/-!
## Example: the bundle is inhabited

The reversible pair `A ⇌ B` of `CRNT.Examples.ReversiblePair` satisfies the whole bundle; the
two numerical conditions are discharged from the deficiency-zero theory and the terminal-linkage
condition by the kernel-reducible decider.
-/

namespace CRNT.DeficiencyOneHypothesesDecideExample

open CRNT
open CRNT.Examples.ReversiblePair

/-- **The reversible pair `A ⇌ B` satisfies the deficiency-one hypothesis bundle.** Conditions
(i) and (ii) follow from the deficiency-zero theory (`δ = 0`, so every class deficiency is `0`
and the class deficiencies sum to `0 = δ`); condition (iii) is decided in the kernel. -/
example : N.DeficiencyOneHypotheses := by
  have hzero : ∀ q, N.linkageDeficiency q = 0 :=
    fun q => N.linkageDeficiency_eq_zero_of_deficiencyZero deficiencyZero q
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro q
    rw [hzero q]
    omega
  · have hs : Finset.sum (@Finset.univ (Quotient N.linkedSetoid)
        (CRNT.Network.instFintypeQuotientLinked N)) (fun q => N.linkageDeficiency q) = 0 :=
      Finset.sum_eq_zero fun q _ => hzero q
    have hd : N.deficiencyInt = 0 := deficiencyZero
    omega
  · decide

/-- The terminal-linkage half of the bundle *is* kernel-`decide`-reducible. -/
example : N.OneTerminalSLCPerLinkageClass := by decide

end CRNT.DeficiencyOneHypothesesDecideExample

/-!
## Example: a deficiency-one network, evaluated by compiled evaluation

The cycle `A → 2A → 3A → A` has three collinear complexes, one linkage class, stoichiometric
rank one, hence deficiency `δ = 3 − 1 − 1 = 1` and class deficiency `δ_θ = 3 − 1 − 1 = 1`: it is
a genuine deficiency-one network, and it satisfies all three structural hypotheses. The decision
is *compiled* (`#eval`), because `computeRank` is a determinant over a permutation sum that the
kernel does not reduce.
-/

namespace CRNT.DeficiencyOneHypothesesDecideExample

open CRNT

inductive Species
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `A`. -/
def c1 : Complex Species := fun s => match s with | A => 1 | B => 0
/-- The complex `2A`. -/
def c2 : Complex Species := fun s => match s with | A => 2 | B => 0
/-- The complex `3A`. -/
def c3 : Complex Species := fun s => match s with | A => 3 | B => 0

inductive Rxn
  | r1
  | r2
  | r3
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2, Rxn.r3}
  complete := by intro r; cases r <;> simp

/-- The three reaction channels of the cycle. -/
def reaction : Rxn → Reaction Species
  | .r1 => { source := c1, target := c2 }
  | .r2 => { source := c2, target := c3 }
  | .r3 => { source := c3, target := c1 }

/-- The deficiency-one network `A → 2A → 3A → A`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

-- **The whole hypothesis bundle holds**, by compiled evaluation of the decider.
#eval decide N.DeficiencyOneHypotheses

-- The network deficiency is one.
#eval N.computableDeficiency

-- The single class deficiency is one.
#eval (Finset.univ : Finset (Quotient N.linkedSetoid)).sum N.computeLinkageDeficiency

end CRNT.DeficiencyOneHypothesesDecideExample

#print axioms CRNT.Network.decidableDeficiencyOneHypotheses
#print axioms CRNT.Network.deficiencyOneHypotheses_iff
#print axioms CRNT.Network.deficiencyOneHypotheses_iff_compute
#print axioms CRNT.Network.finset_univ_linkageClass_eq
#print axioms CRNT.Network.sum_linkageClass_eq_of_fintype
