import CRNT.Decision.Rank
import CRNT.Decision.ComputableDeficiency
import CRNT.Decision.MinorSearch
import Mathlib.Data.List.Sublists

/-!
# The `crnt_deficiency_zero` tactic

A deficiency-zero certificate reduces, by `deficiencyZero_of_minor`, to two obligations:
a `k × k` stoichiometric minor with nonzero rational determinant (witnessing `s ≥ k`), and the count
inequality `n ≤ k + ℓ`. Discharging these by hand is linear algebra an external tool will not write.

This module provides both forms of the tactic:

* `crnt_deficiency_zero f, σ` — the **explicit** form: the caller supplies the witnessing selection
  (`f : Fin k → N.R`, `σ : Fin k → S`) and the tactic proves `N.DeficiencyZero`.
* `crnt_deficiency_zero` — the **argument-free** form: the tactic meta-evaluates `k = n − ℓ`, runs
  the compiled minor search (`findMinorWitness`) to locate a nonsingular minor, builds the selection,
  and discharges as above. The search runs compiled, so the determinant's permutation sum — which
  kernel `decide` cannot reduce — is evaluated directly; the witness it returns is then discharged on
  the kernel path.

Both discharge each obligation on the kernel path: the determinant by `simp` with the closed-form
determinant lemmas (`det_fin_one`/`two`/`three`, with a `det_succ_row_zero` cofactor fallback) under
ground reduction, with the remaining entry arithmetic closed by `decide` or — after `norm_cast`
pushes the casts into `ℤ`, where the kernel evaluates the concrete reaction-vector entries in either
the codegen (inductive `Species`) or the data-driven (`Fin n`) encoding — by `decide`, and the count
by rewriting the
noncomputable `numLinkageClasses` to the evaluable `computeNumLinkageClasses` and then `decide`; no
`native_decide`.

`crnt_stoich_rank_ge f, σ` reuses the same determinant discharge to prove `k ≤ N.stoichRank` from a
nonsingular-minor witness (`stoichRank_ge_of_det_ne_zero`).

Depends on: `CRNT.Decision.Rank`,
`CRNT.Decision.ComputableDeficiency`, `CRNT.Decision.MinorSearch`.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace CRNT

/-- Close a `det ≠ 0` goal for a concrete stoichiometric minor by closed-form expansion under ground
reduction (cofactor fallback for `k ≥ 4`), then discharge the remaining entry arithmetic: `decide`
when the residue is already decidable, otherwise `norm_cast` to push the casts into `ℤ` (where the
kernel evaluates the concrete reaction-vector entries) followed by `decide`. -/
macro "crnt_minor_det" : tactic =>
  `(tactic|
    first
      | (simp +decide [Matrix.det_fin_one, Matrix.det_fin_two, Matrix.det_fin_three]
          <;> first | decide | (norm_cast <;> decide))
      | (simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
          <;> first | decide | (norm_cast <;> decide)))

/-- Close a `N.DeficiencyZero` goal from an explicit nonsingular-minor witness: `f` selects the `k`
reactions and `σ` the `k` species of a stoichiometric minor with nonzero determinant. -/
macro "crnt_deficiency_zero" f:term ", " σ:term : tactic =>
  `(tactic|
    (refine CRNT.Network.deficiencyZero_of_minor _ $f $σ ?_ ?_
     · crnt_minor_det
     · rw [← CRNT.Network.computeNumLinkageClasses_eq_numLinkageClasses]
       decide))

/-- Prove `k ≤ N.stoichRank` from an explicit nonsingular `k × k` minor witness. -/
macro "crnt_stoich_rank_ge" f:term ", " σ:term : tactic =>
  `(tactic| (refine CRNT.Network.stoichRank_ge_of_det_ne_zero _ $f $σ ?_; crnt_minor_det))

/-! ## The argument-free auto-search form

Meta-machinery: evaluate closed `Nat`/witness expressions via compiled execution (the minor search's
determinant cannot reduce in the kernel), enumerate a finite carrier's elements as terms, and build
the `Fin k → _` selection the explicit tactic consumes.
-/

/-- Compiled evaluation of a closed `Nat` expression. -/
unsafe def evalNatImpl (e : Expr) : MetaM Nat :=
  Lean.Meta.evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatImpl]
def evalNatExpr (_ : Expr) : MetaM Nat := pure 0

/-- The reflected type `Option (List Nat × List Nat)`. -/
def witnessType : Expr :=
  let listNat := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0, 0]) listNat listNat)

/-- Compiled evaluation of a `findMinorWitness` call. -/
unsafe def evalWitnessImpl (e : Expr) : MetaM (Option (List Nat × List Nat)) :=
  Lean.Meta.evalExpr (Option (List Nat × List Nat)) witnessType e

@[implemented_by evalWitnessImpl]
def evalWitnessExpr (_ : Expr) : MetaM (Option (List Nat × List Nat)) := pure none

/-- Enumerate the elements of a finite carrier `T` as terms: numerals `⟨i, _⟩` for `Fin n`, or the
constructors of a nullary inductive (the codegen `Species`/`Rxn` shape). -/
def enumCarrier (T : Expr) : MetaM (Option (Array Expr)) := do
  let T ← whnf T
  if T.isAppOf ``Fin then
    let nE := T.appArg!
    let n ← evalNatExpr nE
    let mut out := #[]
    for i in [0:n] do
      let lt ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, nE])
      out := out.push (← mkAppOptM ``Fin.mk #[some nE, some (mkNatLit i), some lt])
    return some out
  else match T.getAppFn.constName? with
    | some nm =>
      let .inductInfo info ← getConstInfo nm | return none
      let lvls := T.getAppFn.constLevels!
      return some (info.ctors.toArray.map (mkConst · lvls))
    | none => return none

/-- Build the vector `![e₀, …, eₖ₋₁] : Fin k → α` from element expressions of type `α`. -/
def mkVec (α : Expr) (elems : List Expr) : MetaM Expr := do
  let mut acc ← mkAppOptM ``Matrix.vecEmpty #[some α]
  for e in elems.reverse do
    acc ← mkAppM ``Matrix.vecCons #[e, acc]
  return acc

/-- The argument-free auto-search certificate: find a nonsingular minor and discharge. -/
elab "crnt_deficiency_zero" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let (declName, args) := (← instantiateMVars (← goal.getType)).getAppFnArgs
    unless declName == ``CRNT.Network.DeficiencyZero && args.size == 4 do
      throwError "crnt_deficiency_zero: goal is not `N.DeficiencyZero`"
    let S := args[0]!
    let N := args[3]!
    let RT ← mkAppM ``CRNT.Network.R #[N]
    let some rElems ← enumCarrier RT | throwError "crnt_deficiency_zero: unsupported reaction carrier"
    let some sElems ← enumCarrier S | throwError "crnt_deficiency_zero: unsupported species carrier"
    let n ← evalNatExpr (← mkAppM ``CRNT.Network.numComplexes #[N])
    let l ← evalNatExpr (← mkAppM ``CRNT.Network.computeNumLinkageClasses #[N])
    let k := n - l
    let rsList ← mkListLit RT rElems.toList
    let ssList ← mkListLit S sElems.toList
    let search ← mkAppM ``CRNT.Network.findMinorWitness #[N, rsList, ssList, mkNatLit k]
    let some (ri, si) ← evalWitnessExpr search
      | throwError "crnt_deficiency_zero: no nonsingular {k}×{k} minor found (deficiency is positive)"
    let f ← mkVec RT (ri.filterMap (rElems[·]?))
    let σ ← mkVec S (si.filterMap (sElems[·]?))
    let lem ← mkAppM ``CRNT.Network.deficiencyZero_of_minor #[N, f, σ]
    let newGoals ← goal.apply lem
    setGoals newGoals
    evalTactic <| ← `(tactic|
      all_goals first
        | (rw [← CRNT.Network.computeNumLinkageClasses_eq_numLinkageClasses]; decide)
        | crnt_minor_det)

end CRNT
