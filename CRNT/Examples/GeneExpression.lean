import Mathlib.Tactic.DeriveFintype
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Stoich.Vector
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction

set_option backward.isDefEq.respectTransparency false

/-!
# Simple gene expression

A mechanistic transcription/translation/degradation network:

```text
DNA → DNA + mRNA      (transcription; DNA acts catalytically)
mRNA → mRNA + Protein (translation; mRNA acts catalytically)
mRNA → 0              (mRNA degradation)
Protein → 0           (protein degradation)
```

It demonstrates source/target complexes, the zero complex, and the mass-action vector
field. As a structural (parameter-independent) fact we prove that the DNA concentration
is conserved by the mass-action dynamics: `d[DNA]/dt = 0` for every rate choice and
every concentration, because DNA appears catalytically.
-/

namespace CRNT.Examples.GeneExpression

open CRNT

/-- Three species: DNA, mRNA, and Protein. -/
inductive Species
  | DNA
  | mRNA
  | Protein
  deriving DecidableEq, Fintype, Repr

open Species

/-- The complex `DNA`. -/
def cDNA : Complex Species := fun s => match s with | DNA => 1 | _ => 0
/-- The complex `DNA + mRNA`. -/
def cDNAmRNA : Complex Species := fun s => match s with | DNA => 1 | mRNA => 1 | _ => 0
/-- The complex `mRNA`. -/
def cmRNA : Complex Species := fun s => match s with | mRNA => 1 | _ => 0
/-- The complex `mRNA + Protein`. -/
def cmRNAProt : Complex Species := fun s => match s with | mRNA => 1 | Protein => 1 | _ => 0
/-- The complex `Protein`. -/
def cProt : Complex Species := fun s => match s with | Protein => 1 | _ => 0

/-- Four reactions: transcription, translation, and two degradations. -/
inductive Rxn
  | transcribe
  | translate
  | degradeMRNA
  | degradeProt
  deriving DecidableEq, Fintype, Repr

/-- The reaction map. The zero complex `Complex.zero` is the target of degradation. -/
def rxn : Rxn → Reaction Species
  | .transcribe  => { source := cDNA,  target := cDNAmRNA }
  | .translate   => { source := cmRNA, target := cmRNAProt }
  | .degradeMRNA => { source := cmRNA, target := Complex.zero }
  | .degradeProt => { source := cProt, target := Complex.zero }

/-- The gene-expression network. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- `n = 5`: the five complexes are `DNA`, `DNA+mRNA`, `mRNA`, `mRNA+Protein`,
`Protein`, and `0` — but `DNA+mRNA` and `mRNA+Protein` together with the others give
five distinct complexes appearing in reactions, plus the zero complex. -/
theorem numComplexes_eq : N.numComplexes = 6 := by decide

/-- Every reaction leaves the DNA coordinate unchanged: DNA is catalytic. -/
theorem reactionVector_DNA_zero (r : N.R) : N.reactionVector r DNA = 0 := by
  cases r <;>
    simp [Network.reactionVector, N, rxn, Reaction.vector,
      cDNA, cDNAmRNA, cmRNA, cmRNAProt, cProt, Complex.zero]

/-- **DNA is conserved.** For every choice of positive rate constants and every
concentration, the mass-action rate of change of DNA is zero. This is a structural,
parameter-independent property obtained directly from the reaction vectors. -/
theorem dDNA_dt_eq_zero (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x DNA = 0 := by
  rw [Network.massActionVectorField_apply]
  apply Finset.sum_eq_zero
  intro r _
  rw [reactionVector_DNA_zero r, mul_zero]

end CRNT.Examples.GeneExpression
