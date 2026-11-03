import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic
import CRNT.Kinetics.MassAction
import CRNT.Equilibria.SteadyState

/-!
# Perfect adaptation via antithetic integral feedback

The antithetic integral feedback (AIF) motif of Briat, Gupta, and Khammash realises
perfect adaptation: at any steady state the sensed output is pinned to a setpoint that
depends only on the controller reference and sensing rates, independent of every other
rate constant.

The motif is modelled as a concrete `Network` over three species — two controller
species `Z1`, `Z2` and the output `X` — with three reactions:

```text
ref:   0 → Z1            (constant reference production at rate κ.ref)
sense: X → X + Z2        (output catalytically produces the sensing species Z2)
seq:   Z1 + Z2 → 0       (mutual sequestration)
```

The actuation reaction `Z1 → Z1 + X` linking the controller to the plant is omitted:
the setpoint property is a balance condition on the controller species `Z1` and `Z2`
alone, so the motif is a drop-in controller agnostic to the plant producing or
consuming `X`. At steady state the two controller production rates are equal,
`κ.sense * x_X = κ.ref`, which fixes the output `x_X = κ.ref / κ.sense`.

Depends on: `CRNT.Kinetics.MassAction`,
`CRNT.Equilibria.SteadyState`.
-/

namespace CRNT.Design.Adaptation

open CRNT

/-- Three species: the two controller species `Z1`, `Z2` and the output `X`. -/
inductive Species
  | Z1
  | Z2
  | X
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.Z1, Species.Z2, Species.X}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `Z1`. -/
def cZ1 : Complex Species := fun s => match s with | Z1 => 1 | _ => 0
/-- The complex `Z1 + Z2`, the source of the sequestration reaction. -/
def cZ1Z2 : Complex Species := fun s => match s with | Z1 => 1 | Z2 => 1 | _ => 0
/-- The complex `X`, the catalytic source of the sensing reaction. -/
def cX : Complex Species := fun s => match s with | X => 1 | _ => 0
/-- The complex `X + Z2`, the target of the sensing reaction. -/
def cXZ2 : Complex Species := fun s => match s with | X => 1 | Z2 => 1 | _ => 0

/-- Three reactions: reference production, sensing, and sequestration. -/
inductive Rxn
  | ref
  | sense
  | seq
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.ref, Rxn.sense, Rxn.seq}
  complete := by intro r; cases r <;> simp

/-- The reaction map: `ref` is `0 → Z1`, `sense` is `X → X + Z2`, and `seq` is
`Z1 + Z2 → 0`. -/
def rxn : Rxn → Reaction Species
  | .ref   => { source := Complex.zero, target := cZ1 }
  | .sense => { source := cX,           target := cXZ2 }
  | .seq   => { source := cZ1Z2,        target := Complex.zero }

/-- The antithetic integral feedback network. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- A sum over the three reactions expands to the sum of its three summands. -/
theorem sum_Rxn (f : Rxn → ℝ) :
    (∑ r : Rxn, f r) = f Rxn.ref + f Rxn.sense + f Rxn.seq := by
  rw [show (Finset.univ : Finset Rxn) = {Rxn.ref, Rxn.sense, Rxn.seq} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- The sensing monomial reduces to the output concentration: `cX` has `X` with
coefficient one and every other species with coefficient zero. -/
theorem sense_mono (x : Concentration Species) :
    cX.massActionMonomial x = x Species.X := by
  rw [Complex.massActionMonomial]
  rw [show (Finset.univ : Finset Species) = {Z1, Z2, X} from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp [cX]

/-- The vector field at `Z1`: constant reference production minus sequestration. -/
theorem vf_Z1 (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x Species.Z1 =
      κ.k .ref - κ.k .seq * cZ1Z2.massActionMonomial x := by
  rw [Network.massActionVectorField_apply]
  rw [show (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r Species.Z1) =
    (∑ r : Rxn, N.massActionRate κ r x * N.reactionVector r Species.Z1) from rfl]
  rw [sum_Rxn]
  simp only [Network.massActionRate, Network.reactionVector, Reaction.vector, N, rxn,
    cZ1, cZ1Z2, cX, cXZ2, Complex.zero, Complex.massActionMonomial_zero]
  push_cast
  ring

/-- The vector field at `Z2`: sensing production minus sequestration. -/
theorem vf_Z2 (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x Species.Z2 =
      κ.k .sense * cX.massActionMonomial x - κ.k .seq * cZ1Z2.massActionMonomial x := by
  rw [Network.massActionVectorField_apply]
  rw [show (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r Species.Z2) =
    (∑ r : Rxn, N.massActionRate κ r x * N.reactionVector r Species.Z2) from rfl]
  rw [sum_Rxn]
  simp only [Network.massActionRate, Network.reactionVector, Reaction.vector, N, rxn,
    cZ1, cZ1Z2, cX, cXZ2, Complex.zero, Complex.massActionMonomial_zero]
  push_cast
  ring

/-- **Setpoint invariance (integral feedback property).** At any mass-action steady
state the two controller production rates are equal: the sensed output rate
`κ.sense * x_X` equals the reference rate `κ.ref`. The shared sequestration monomial
and every other rate constant cancel. -/
theorem setpoint (κ : Network.RateConstants N) (x : Concentration Species)
    (hss : N.IsMassActionSteadyState κ x) :
    κ.k .sense * x Species.X = κ.k .ref := by
  have h1 := hss Species.Z1
  have h2 := hss Species.Z2
  rw [vf_Z1] at h1
  rw [vf_Z2, sense_mono] at h2
  linarith

/-- **Setpoint value.** The sensed output is pinned at `κ.ref / κ.sense`, independent
of the sequestration rate and of any plant dynamics. -/
theorem setpoint_value (κ : Network.RateConstants N) (x : Concentration Species)
    (hss : N.IsMassActionSteadyState κ x) :
    x Species.X = κ.k .ref / κ.k .sense := by
  have h := setpoint κ x hss
  have hpos : 0 < κ.k .sense := κ.positive .sense
  field_simp
  linarith

/-- With reference rate `2` and sensing rate `1`, any steady state pins the output to
`2`, regardless of the sequestration rate. -/
example (x : Concentration Species)
    (κ : Network.RateConstants N)
    (href : κ.k .ref = 2) (hsense : κ.k .sense = 1)
    (hss : N.IsMassActionSteadyState κ x) :
    x Species.X = 2 := by
  have h := setpoint_value κ x hss
  rw [href, hsense] at h
  simpa using h

/-- Two rate-constant choices differing only in the sequestration rate yield the same
setpoint: the controlled output is independent of `κ.seq`. -/
example (x y : Concentration Species)
    (κ₁ κ₂ : Network.RateConstants N)
    (hxss : N.IsMassActionSteadyState κ₁ x)
    (hyss : N.IsMassActionSteadyState κ₂ y)
    (href : κ₁.k .ref = κ₂.k .ref) (hsense : κ₁.k .sense = κ₂.k .sense) :
    x Species.X = y Species.X := by
  rw [setpoint_value κ₁ x hxss, setpoint_value κ₂ y hyss, href, hsense]

end CRNT.Design.Adaptation
