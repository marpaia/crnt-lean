import CRNT
import CRNT.Examples.Lotka

/-!
# Non-vacuity, Lotka witness

These checks run under `lake test`. They are a negative control for the exclusion
route: the Lotka network really does have positive periodic orbits (Lotka-Volterra has a first
integral whose positive level sets are closed curves), so a `noPositivePeriodicOrbitCertified` flag
that reported `true` here would be reporting a falsehood, not merely being uninformative.
-/

open CRNT

namespace CRNT.Test.LotkaNonVacuity

/-! ## Both exclusion routes fail on the Lotka network

`CRNT/Examples/Lotka.lean` proves that the Lotka network is not weakly reversible and has
stoichiometric rank at least two, so neither compiled exclusion route applies to it. That is the
strongest available negative control for `noPositivePeriodicOrbitCertified`: the network really
does oscillate (Lotka–Volterra has a first integral whose level sets are closed curves), so a flag
that reported `true` here would be reporting a falsehood rather than merely being uninformative.

Not `decide`-based, so it exercises the theorem rather than the Boolean. -/

example : ¬ CRNT.Examples.Lotka.N.WeaklyReversible :=
  CRNT.Examples.Lotka.not_weaklyReversible

example : 2 ≤ CRNT.Examples.Lotka.N.stoichRank :=
  CRNT.Examples.Lotka.two_le_stoichRank

example : ¬ CRNT.Examples.Lotka.N.WeaklyReversible ∧ 2 ≤ CRNT.Examples.Lotka.N.stoichRank :=
  CRNT.Examples.Lotka.exclusion_routes_do_not_apply

/-- The conservation identity itself, as a test: at every positive concentration the first integral
of the Lotka system has vanishing derivative along the field. This is the algebraic heart of the
non-vacuity witness, and it is unconditional. -/
example (κ : CRNT.Network.RateConstants CRNT.Examples.Lotka.N)
    {x : CRNT.Concentration CRNT.Examples.Lotka.Species} (hx : x.Positive) :
    (∑ s, CRNT.Examples.Lotka.firstIntegralGrad κ x s *
      CRNT.Examples.Lotka.N.massActionVectorField κ x s) = 0 :=
  CRNT.Examples.Lotka.conservation_identity κ hx


end CRNT.Test.LotkaNonVacuity
