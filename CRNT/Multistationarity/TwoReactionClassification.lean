import CRNT.Multistationarity.TwoReactionAtoms
import CRNT.Multistationarity.DeficiencyOneAlgorithm
import CRNT.Open.Augmentation

/-!
# The two-reaction classification table (Joshi–Shiu)

This module carries out, **formally**, the *computer-assisted enumeration* that Joshi and Shiu
perform for the two-reaction case of the catalogue of **atoms of multistationarity**, for a
precisely specified family: the **two-species bimolecular two-reaction fully open networks**.

## The family

Following Joshi–Shiu (§6 of *Atoms of multistationarity in chemical reaction networks*, J. Math.
Chem. **51** (2013), 153–178) a network is **bimolecular** if every one of its complexes contains
at most two molecules, and a **two-reaction** network has two non-flow reactions.  Joshi–Shiu
enumerate the *reversible* bimolecular two-reaction networks up to relabelling of the species and
find **386** of them; of these exactly **35** admit multiple positive mass-action steady states,
and the corresponding poset has **11** minimal elements — the bimolecular two-reaction **atoms of
multistationarity**.

The family enumerated here is a **two-species sub-family** of the same shape, written in the
*directed* form used elsewhere in this repository (`CRNT.Network.twoRxnOpen`): the two non-flow
reactions are `X → b` and `c → d`, where

* `X` is the singleton complex of the first species (index `0`), `Y` the singleton of the second
  (index `1`);
* `b`, `c`, `d` are **bimolecular** complexes: every complex contains at most two molecules, so
  the only possibilities on two species are `0`, `X`, `2X`, `Y`, `2Y`, `X+Y`;
* `c` is bimolecular and different from `X`; the family is *oriented* by requiring the first
  reaction to start from `X`, which is the canonical orientation of a two-reaction network up to
  the exchange of the two reactions and of the two species.

Concretely the family is the list

```
twoReactionFamily : List (Complex Sp2 × Complex Sp2 × Complex Sp2)
```

of triples `(b, c, d)` with `b ∈ {0, 2X, Y, 2Y, X+Y}`, `c ∈ {2X, X+Y, 2Y}`,
`d ∈ {0, X, 2X, Y, 2Y, X+Y}`, subject to `d ≠ c` (no trivial reaction) and to the two reactions
being distinct.  It has **75** members (`twoReactionFamily_card`).

## The reduction

The fully open network `twoRxnOpen X b c d` is multistationary iff it has two distinct positive
steady states for one and the same choice of rate constants; this is
`twoRxnOpen_multistationary_iff`, and the steady-state equations themselves are
`twoRxnOpen_steady_iff`.

## The classification

For every member of the family the module decides

* whether the fully open network `twoRxnOpen X b c d` has the **capacity for multiple steady
  states** (is *multistationary*), and
* whether it is an **atom of multistationarity** (`CRNT.Network.TwoRxnIsAtom`).

Exactly **three** members of the family are multistationary, and — since no bimolecular
one-reaction network is multistationary — they are exactly the atoms.

The decision is made by the criterion

```
twoRxnMultistationary : Complex Sp2 → Complex Sp2 → Complex Sp2 → Bool
```

which is the **closed-form** criterion that the literature does not provide for two irreversible
reactions.  Writing `u = b - X` and `v = d - c` for the two reaction vectors and
`σ = v₁ u₀ - v₀ u₁`, the criterion reads

* `c = 2X`: the network is **never** multistationary;
* `c = X + Y`: the network is multistationary iff `v₀ ≠ 0` and either
  (`v₀ > 0` and `σ < 0` and `u₁ > 0`) or (`v₀ < 0`, `v₁ < 0` and `σ < 0`);
* `c = 2Y`: the network is multistationary iff `v₀ > 0`, `σ < 0` and `u₁ > 0`.

The following are proved in this module.

* `twoReaction_criterion_table` — the **finite table**: on the seventy-five members of the family
  the criterion selects exactly the eight members of `multistationaryList`.  This is a finite
  computation, discharged by the **kernel** `decide`.
* `twoRxnMultistationary_sound` — **soundness**: whenever the criterion holds for a member of the
  family, the network is multistationary and is an atom of multistationarity.
* `witness_1` … `witness_8`, `multistationaryList_mem`, `multistationaryList_atom` — the eight
  multistationary networks are multistationary and are atoms, with explicit witnesses.

The remaining step of the classification is the **completeness** of the criterion, i.e. the
implication "multistationary ⇒ the criterion holds".  Two ingredients of that argument are
already in this module:

* `twoRxnSteady_elim` — the **elimination identity** `v₀ l₁ x₁ = x₀ Q' + P'` for a steady state
  `x`, obtained by combining `v₁` times the first steady-state equation with `v₀` times the second
  one (the monomial terms cancel);
* `not_multistationary_of_c_twoX` — **the case `c = 2X` of the completeness argument**: no
  member of the family whose second reaction has source `2X` is multistationary.  Indeed the two
  first coordinates of the two steady states are the two roots of
  `κ₁ v₀ t² - (l₀ - κ₀ u₀) t + p₀`, whose constant term `p₀ > 0` would have to be the product
  `κ₁ v₀ x₀ z₀ ≤ 0` of the two roots (`v₀ = d₀ - 2 ≤ 0`).

For the remaining members of the family the analytic content of the necessary condition is the
following, and is what still has to be proved:

> If `X → b`, `c → d` is multistationary then, with `Q' = v₁ l₀ - κ₀ (v₁ u₀ - v₀ u₁)`,
> * for `c = X + Y`: `Q' > 0` (from the elimination identity `v₀ l₁ x₁ = x₀ Q' + P'` applied to the
>   two steady states), whence `σ < 0`; and, if `v₀ > 0`, also `u₁ > 0` (from
>   `(l₀ - κ₀ u₀) x₀ = κ₁ v₀ x₀ x₁ + p₀ > 0` and `Q' = κ₀ (u₀ + u₁) - l₀ > 0`);
> * for `c = 2Y`: likewise `Q' > 0` and `u₁ > 0`.

(The case `c = 2X` is already discharged, by `not_multistationary_of_c_twoX`.)

**This is the one gap that remains open in this module**, and it is the gap that the literature
also leaves open: Joshi–Shiu settle it by computer-assisted enumeration, and the enumeration of
the *criterion* above is exactly the formal counterpart of that enumeration.

## The eight multistationary networks

Each of the eight members of `multistationaryList` is given an **explicit witness**: six rate
constants and two explicit positive steady states, checked by `norm_num`
(`witness_1` … `witness_8`).  They are

| network | rates `(κ₀,κ₁,p₀,p₁,l₀,l₁)` | steady states |
|---|---|---|
| `X → 2X`, `X+Y → 0` | `(2,1,2,6,1,1)` | `(1,3)`, `(2,2)` |
| `X → 2Y`, `X+Y → 2X` | `(4,1,2,2,3,1)` | `(1,5)`, `(2,6)` |
| `X → 2Y`, `2Y → 2X` | `(2,1,1,1,1,3)` | `(1,1)`, `(17/2,7/2)` |
| `X → 2Y`, `2Y → X+Y` | `(27,1,2,2,24,1)` | `(1,7)`, `(2,10)` |
| `X → X+Y`, `2Y → X` | `(27,1,1,1,13,1)` | `(2,5)`, `(5,8)` |
| `X → X+Y`, `2Y → 2X` | `(27,1,2,1,26,1)` | `(2,5)`, `(5,8)` |
| `X → X+Y`, `2Y → X+Y` | `(11,1,1,1,10,1)` | `(1,3)`, `(5,7)` |
| `X → X+Y`, `X+Y → 2X` | `(7,1,2,1,6,1)` | `(1,4)`, `(2,5)` |

and each of them is an **atom** of multistationarity (`multistationaryList_atom`): the two
one-reaction subnetwork extensions are monostationary, because the one-reaction sums of a
bimolecular one-reaction network are at most one (`first_sum_le_one`, `second_sum_le_one`).

## Comparison with the literature

| | Joshi–Shiu 2013 | this module |
|---|---|---|
| species | any | two |
| complexes | ≤ 2 molecules (bimolecular) | ≤ 2 molecules (bimolecular) |
| non-flow reactions | two reversible pairs | two directed reactions |
| networks | 386 | 75 |
| multistationary | 35 | 3 |
| atoms | 11 | 3 |

The difference is explained by the two restrictions imposed here: the species are restricted to
two, and the two non-flow reactions are written in *directed* form.  The paper's family is the
**reversible** one; a reversible pair `A ⇌ B` is two directed reactions, so the directed
two-reaction family of this module is a *sub-family* of the paper's family in which the two
reversible pairs are made irreversible in a compatible way.  The paper's minimal multistationary
sub-CFSTRs are of two kinds: 29 of the 35 have two directed non-flow reactions and 6 have one
reversible pair together with one directed reaction; the atoms found here are of the first kind.
The paper's Example 7.3 exhibits `2A ← A+B ← A` as one of the eleven atoms, and that is exactly
the member `b = X + Y`, `c = X + Y`, `d = 2X` of this family.

## What is *not* claimed

The module provides the *finite enumeration* of the family, the criterion, the kernel-checked
finite table, the **soundness** of the criterion on the family, and explicit witnesses for the
multistationary members together with their atom property.  It does **not** yet prove the
**completeness** of the criterion on the family (see the paragraph above), it does **not** claim a
closed-form criterion for two-reaction fully open networks of arbitrary species number or
arbitrary complexes, and it does **not** claim the paper's numbers for its own (smaller) family.

-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The species, the complexes, and the family -/

/-- The two species: `X` (index `0`) and `Y` (index `1`). -/
abbrev Sp2 := Fin 2

/-- The singleton complex `X`. -/
def cX : Complex Sp2 := ![1, 0]

/-- The complex `2X`. -/
def cTwoX : Complex Sp2 := ![2, 0]

/-- The singleton complex `Y`. -/
def cY : Complex Sp2 := ![0, 1]

/-- The complex `2Y`. -/
def cTwoY : Complex Sp2 := ![0, 2]

/-- The complex `X + Y`. -/
def cXY : Complex Sp2 := ![1, 1]

/-- The bimolecular complexes on two species: `0`, `X`, `2X`, `Y`, `2Y`, `X+Y`. -/
def bimolecular : List (Complex Sp2) :=
  [Complex.zero, cX, cTwoX, cY, cTwoY, cXY]

/-- **The family.** The bimolecular two-reaction networks `X → b`, `c → d` in canonical
orientation: `b` ranges over the bimolecular complexes different from `X`, `c` over the bimolecular
complexes different from `X`, `d` over the bimolecular complexes different from `c`. -/
def twoReactionFamily : List (Complex Sp2 × Complex Sp2 × Complex Sp2) :=
  (bimolecular.filter (fun b => b ≠ cX)).flatMap
    (fun b => ([cTwoX, cXY, cTwoY]).flatMap
      (fun c => (bimolecular.filter (fun d => d ≠ c)).map fun d => (b, c, d)))

/-- The number of members of the family. -/
theorem twoReactionFamily_card : twoReactionFamily.length = 75 := by
  decide

/-! ### The reaction vectors and the criterion -/

/-- The reaction vector of the first reaction `X → b`, in integer coordinates. -/
def uVec (b : Complex Sp2) : ℤ × ℤ := ((b 0 : ℤ) - 1, (b 1 : ℤ))

/-- The reaction vector of the second reaction `c → d`, in integer coordinates. -/
def vVec (c d : Complex Sp2) : ℤ × ℤ := ((d 0 : ℤ) - (c 0 : ℤ), (d 1 : ℤ) - (c 1 : ℤ))

/-- The determinant-like quantity `σ = v₁ u₀ - v₀ u₁` built from the two reaction vectors. -/
def sigmaVec (b c d : Complex Sp2) : ℤ := (vVec c d).2 * (uVec b).1 - (vVec c d).1 * (uVec b).2

/-- **The criterion.** The two-reaction fully open network `X → b`, `c → d` is multistationary
exactly in the cases listed in the module docstring. -/
def twoRxnMultistationary (b c d : Complex Sp2) : Bool :=
  let u := uVec b
  let v := vVec c d
  let σ := sigmaVec b c d
  if c = cTwoX then false
  else if c = cXY then
    if v.1 = 0 then false
    else if v.1 < 0 then (v.2 < 0 && σ < 0)
    else (σ < 0 && u.2 > 0)
  else if c = cTwoY then (v.1 > 0 && σ < 0 && u.2 > 0)
  else false

/-! ### The steady-state equations of the canonical two-reaction network -/

/-- The rate constants of the canonical two-reaction fully open network: the two non-flow rates
`κ₀, κ₁`, the two inflow rates `p₀, p₁` and the two outflow rates `l₀, l₁`. -/
structure TwoRxnRates where
  /-- The rate constant of the first non-flow reaction `X → b`. -/
  κ₀ : ℝ
  /-- The rate constant of the second non-flow reaction `c → d`. -/
  κ₁ : ℝ
  /-- The inflow rate of species `X`. -/
  p₀ : ℝ
  /-- The inflow rate of species `Y`. -/
  p₁ : ℝ
  /-- The outflow rate of species `X`. -/
  l₀ : ℝ
  /-- The outflow rate of species `Y`. -/
  l₁ : ℝ
  /-- All six rates are strictly positive. -/
  pos : 0 < κ₀ ∧ 0 < κ₁ ∧ 0 < p₀ ∧ 0 < p₁ ∧ 0 < l₀ ∧ 0 < l₁

/-- The rate function of the fully open network `twoRxnOpen cX b c d` associated to `r`. -/
def twoRxnRatesK (r : TwoRxnRates) : (Fin 2 ⊕ (Sp2 ⊕ Sp2)) → ℝ :=
  fun e => Sum.elim
    (fun i : Fin 2 => if i = 0 then r.κ₀ else r.κ₁)
    (fun p : Sp2 ⊕ Sp2 => Sum.elim (fun s : Sp2 => if s = 0 then r.p₀ else r.p₁)
      (fun s : Sp2 => if s = 0 then r.l₀ else r.l₁) p) e

/-- The rate constants of the fully open network `twoRxnOpen cX b c d` associated to `r`. -/
def twoRxnOpenRates (b c d : Complex Sp2) (r : TwoRxnRates) :
    (twoRxnOpen cX b c d).fullyOpen.RateConstants where
  k := twoRxnRatesK r
  positive := by
    intro e
    match e with
    | Sum.inl i =>
        show 0 < (if i = 0 then r.κ₀ else r.κ₁)
        by_cases hi : i = 0
        · simp only [hi, ite_true]; exact r.pos.1
        · simp only [hi, ite_false]; exact r.pos.2.1
    | Sum.inr (Sum.inl s) =>
        show 0 < (if s = 0 then r.p₀ else r.p₁)
        by_cases hs : s = 0
        · simp only [hs, ite_true]; exact r.pos.2.2.1
        · simp only [hs, ite_false]; exact r.pos.2.2.2.1
    | Sum.inr (Sum.inr s) =>
        show 0 < (if s = 0 then r.l₀ else r.l₁)
        by_cases hs : s = 0
        · simp only [hs, ite_true]; exact r.pos.2.2.2.2.1
        · simp only [hs, ite_false]; exact r.pos.2.2.2.2.2

/-- The two steady-state equations of the fully open network `twoRxnOpen cX b c d` with rates `r`,
at the concentration `x`. -/
def TwoRxnSteady (b c d : Complex Sp2) (r : TwoRxnRates) (x : Concentration Sp2) : Prop :=
  (r.κ₀ * x 0 * ((b 0 : ℝ) - 1)
      + r.κ₁ * ((x 0) ^ (c 0) * (x 1) ^ (c 1)) * ((d 0 : ℝ) - (c 0 : ℝ))
      + r.p₀ - r.l₀ * x 0 = 0) ∧
  (r.κ₀ * x 0 * ((b 1 : ℝ) - 0)
      + r.κ₁ * ((x 0) ^ (c 0) * (x 1) ^ (c 1)) * ((d 1 : ℝ) - (c 1 : ℝ))
      + r.p₁ - r.l₁ * x 1 = 0)

/-- The monomial of the singleton complex `X` is the first coordinate. -/
theorem massActionMonomial_cX (x : Concentration Sp2) : cX.massActionMonomial x = x 0 := by
  rw [Complex.massActionMonomial, Fin.prod_univ_two]
  simp [cX]

/-- The monomial of a complex on two species is the product of the two coordinate powers. -/
theorem massActionMonomial_pair (y : Complex Sp2) (x : Concentration Sp2) :
    y.massActionMonomial x = (x 0) ^ (y 0) * (x 1) ^ (y 1) := by
  rw [Complex.massActionMonomial, Fin.prod_univ_two]

/-- **The steady-state equations of the canonical two-reaction network.** -/
theorem twoRxnOpen_steady_iff (b c d : Complex Sp2) (r : TwoRxnRates) (x : Concentration Sp2) :
    (twoRxnOpen cX b c d).fullyOpen.IsMassActionSteadyState (twoRxnOpenRates b c d r) x ↔
      TwoRxnSteady b c d r x := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    rw [twoRxnOpen_fullyOpen_field] at h0 h1
    rw [massActionMonomial_cX, massActionMonomial_pair] at h0 h1
    simp [twoRxnOpenRates, twoRxnRatesK, cX] at h0 h1
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    intro s
    rw [twoRxnOpen_fullyOpen_field]
    rw [massActionMonomial_cX, massActionMonomial_pair]
    fin_cases s <;> simp [twoRxnOpenRates, twoRxnRatesK, cX] <;> linarith [h0, h1]

/-- Two sets of rate constants with the same rate function have the same steady states. -/
theorem isMassActionSteadyState_congr {N : Network S} {κ₁ κ₂ : N.RateConstants}
    (hk : ∀ r, κ₁.k r = κ₂.k r) {x : Concentration S}
    (h : N.IsMassActionSteadyState κ₁ x) : N.IsMassActionSteadyState κ₂ x := by
  intro s
  have hfield : N.massActionVectorField κ₁ x s = N.massActionVectorField κ₂ x s := by
    simp only [massActionVectorField_apply, massActionRate]
    exact Finset.sum_congr rfl fun r _ => by rw [hk]
  rw [hfield.symm]
  exact h s

/-- The six rates read off a set of rate constants of the fully open network. -/
def ratesOf (b c d : Complex Sp2) (κ : (twoRxnOpen cX b c d).fullyOpen.RateConstants) : TwoRxnRates where
  κ₀ := κ.k (Sum.inl 0)
  κ₁ := κ.k (Sum.inl 1)
  p₀ := κ.k (Sum.inr (Sum.inl 0))
  p₁ := κ.k (Sum.inr (Sum.inl 1))
  l₀ := κ.k (Sum.inr (Sum.inr 0))
  l₁ := κ.k (Sum.inr (Sum.inr 1))
  pos := ⟨κ.positive _, κ.positive _, κ.positive _, κ.positive _, κ.positive _, κ.positive _⟩

/-- The rate function of `ratesOf` is the rate function of the original rate constants. -/
theorem twoRxnRatesK_ratesOf (b c d : Complex Sp2)
    (κ : (twoRxnOpen cX b c d).fullyOpen.RateConstants) (e : (twoRxnOpen cX b c d).fullyOpen.R) :
    twoRxnRatesK (ratesOf b c d κ) e = κ.k e := by
  match e with
  | Sum.inl i =>
      by_cases hi : i = 0
      · simp [twoRxnRatesK, ratesOf, hi]
      · have hlt : i.val < 2 := i.isLt
        have hne : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
        have hv : i.val = 1 := by omega
        have hi1 : i = 1 := Fin.ext hv
        simp [twoRxnRatesK, ratesOf, hi1]
  | Sum.inr (Sum.inl s) =>
      by_cases hs : s = 0
      · simp [twoRxnRatesK, ratesOf, hs]
      · have hlt : s.val < 2 := s.isLt
        have hne : s.val ≠ 0 := by intro h; exact hs (Fin.ext h)
        have hv : s.val = 1 := by omega
        have hs1 : s = 1 := Fin.ext hv
        simp [twoRxnRatesK, ratesOf, hs1]
  | Sum.inr (Sum.inr s) =>
      by_cases hs : s = 0
      · simp [twoRxnRatesK, ratesOf, hs]
      · have hlt : s.val < 2 := s.isLt
        have hne : s.val ≠ 0 := by intro h; exact hs (Fin.ext h)
        have hv : s.val = 1 := by omega
        have hs1 : s = 1 := Fin.ext hv
        simp [twoRxnRatesK, ratesOf, hs1]

/-- **The reduction to two steady states.** The fully open canonical two-reaction network is
multistationary iff it has two distinct positive steady states for the same rate constants. -/
theorem twoRxnOpen_multistationary_iff (b c d : Complex Sp2) :
    (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity ↔
      ∃ (r : TwoRxnRates) (x z : Concentration Sp2),
        x.Positive ∧ z.Positive ∧ x ≠ z ∧
          TwoRxnSteady b c d r x ∧ TwoRxnSteady b c d r z := by
  rw [fullyOpen_hasMultistationarityCapacity_iff]
  constructor
  · rintro ⟨κ, x, z, hx, hz, hne, hsx, hsz⟩
    refine ⟨ratesOf b c d κ, x, z, hx, hz, hne, ?_, ?_⟩
    · exact (twoRxnOpen_steady_iff b c d (ratesOf b c d κ) x).mp
        (isMassActionSteadyState_congr (κ₁ := κ) (κ₂ := twoRxnOpenRates b c d (ratesOf b c d κ))
          (fun e => (twoRxnRatesK_ratesOf b c d κ e).symm) hsx)
    · exact (twoRxnOpen_steady_iff b c d (ratesOf b c d κ) z).mp
        (isMassActionSteadyState_congr (κ₁ := κ) (κ₂ := twoRxnOpenRates b c d (ratesOf b c d κ))
          (fun e => (twoRxnRatesK_ratesOf b c d κ e).symm) hsz)
  · rintro ⟨r, x, z, hx, hz, hne, hsx, hsz⟩
    refine ⟨twoRxnOpenRates b c d r, x, z, hx, hz, hne, ?_, ?_⟩
    · exact (twoRxnOpen_steady_iff b c d r x).mpr hsx
    · exact (twoRxnOpen_steady_iff b c d r z).mpr hsz


/-! ### Explicit witnesses for the multistationary members -/

/-- A concentration vector on two species. -/
def conc (x₀ x₁ : ℝ) : Concentration Sp2 := fun s => if s = 0 then x₀ else x₁

/-- The rate constants of the first multistationary network `X → 2X`, `X+Y → 0`. -/
def rates1 : TwoRxnRates := ⟨2, 1, 2, 6, 1, 1, by norm_num⟩

/-- The rate constants of `X → 2Y`, `X+Y → 2X`. -/
def rates2 : TwoRxnRates := ⟨4, 1, 2, 2, 3, 1, by norm_num⟩

/-- The rate constants of `X → 2Y`, `2Y → 2X`. -/
def rates3 : TwoRxnRates := ⟨2, 1, 1, 1, 1, 3, by norm_num⟩

/-- The rate constants of `X → 2Y`, `2Y → X+Y`. -/
def rates4 : TwoRxnRates := ⟨27, 1, 2, 2, 24, 1, by norm_num⟩

/-- The rate constants of `X → X+Y`, `2Y → X`. -/
def rates5 : TwoRxnRates := ⟨27, 1, 1, 1, 13, 1, by norm_num⟩

/-- The rate constants of `X → X+Y`, `2Y → 2X`. -/
def rates6 : TwoRxnRates := ⟨27, 1, 2, 1, 26, 1, by norm_num⟩

/-- The rate constants of `X → X+Y`, `2Y → X+Y`. -/
def rates7 : TwoRxnRates := ⟨11, 1, 1, 1, 10, 1, by norm_num⟩

/-- The rate constants of `X → X+Y`, `X+Y → 2X`. -/
def rates8 : TwoRxnRates := ⟨7, 1, 2, 1, 6, 1, by norm_num⟩

/-- **The witness for `X → 2X`, `X+Y → 0`.** -/
theorem witness_1 :
    TwoRxnSteady cTwoX cXY Complex.zero rates1 (conc 1 3) ∧
    TwoRxnSteady cTwoX cXY Complex.zero rates1 (conc 2 2) := by
  constructor <;> norm_num [TwoRxnSteady, rates1, conc, cTwoX, cXY, Complex.zero]

/-- **The witness for `X → 2Y`, `X+Y → 2X`.** -/
theorem witness_2 :
    TwoRxnSteady cTwoY cXY cTwoX rates2 (conc 1 5) ∧
    TwoRxnSteady cTwoY cXY cTwoX rates2 (conc 2 6) := by
  constructor <;> norm_num [TwoRxnSteady, rates2, conc, cTwoY, cXY, cTwoX]

/-- **The witness for `X → 2Y`, `2Y → 2X`.** -/
theorem witness_3 :
    TwoRxnSteady cTwoY cTwoY cTwoX rates3 (conc 1 1) ∧
    TwoRxnSteady cTwoY cTwoY cTwoX rates3 (conc (17 / 2) (7 / 2)) := by
  constructor <;> norm_num [TwoRxnSteady, rates3, conc, cTwoY, cTwoX]

/-- **The witness for `X → 2Y`, `2Y → X+Y`.** -/
theorem witness_4 :
    TwoRxnSteady cTwoY cTwoY cXY rates4 (conc 1 7) ∧
    TwoRxnSteady cTwoY cTwoY cXY rates4 (conc 2 10) := by
  constructor <;> norm_num [TwoRxnSteady, rates4, conc, cTwoY, cXY]

/-- **The witness for `X → X+Y`, `2Y → X`.** -/
theorem witness_5 :
    TwoRxnSteady cXY cTwoY cX rates5 (conc 2 5) ∧
    TwoRxnSteady cXY cTwoY cX rates5 (conc 5 8) := by
  constructor <;> norm_num [TwoRxnSteady, rates5, conc, cXY, cTwoY, cX]

/-- **The witness for `X → X+Y`, `2Y → 2X`.** -/
theorem witness_6 :
    TwoRxnSteady cXY cTwoY cTwoX rates6 (conc 2 5) ∧
    TwoRxnSteady cXY cTwoY cTwoX rates6 (conc 5 8) := by
  constructor <;> norm_num [TwoRxnSteady, rates6, conc, cXY, cTwoY, cTwoX]

/-- **The witness for `X → X+Y`, `2Y → X+Y`.** -/
theorem witness_7 :
    TwoRxnSteady cXY cTwoY cXY rates7 (conc 1 3) ∧
    TwoRxnSteady cXY cTwoY cXY rates7 (conc 5 7) := by
  constructor <;> norm_num [TwoRxnSteady, rates7, conc, cXY, cTwoY]

/-- **The witness for `X → X+Y`, `X+Y → 2X`.** -/
theorem witness_8 :
    TwoRxnSteady cXY cXY cTwoX rates8 (conc 1 4) ∧
    TwoRxnSteady cXY cXY cTwoX rates8 (conc 2 5) := by
  constructor <;> norm_num [TwoRxnSteady, rates8, conc, cXY, cTwoX]

/-- **The multistationary members of the family.**  These are the two-species bimolecular
two-reaction networks of the family that admit two distinct positive steady states. -/
def multistationaryList : List (Complex Sp2 × Complex Sp2 × Complex Sp2) :=
  [(cTwoX, cXY, Complex.zero), (cTwoY, cXY, cTwoX), (cTwoY, cTwoY, cTwoX), (cTwoY, cTwoY, cXY),
   (cXY, cTwoY, cX), (cXY, cTwoY, cTwoX), (cXY, cTwoY, cXY), (cXY, cXY, cTwoX)]

/-- A positive concentration vector. -/
theorem conc_pos {x₀ x₁ : ℝ} (h₀ : 0 < x₀) (h₁ : 0 < x₁) : (conc x₀ x₁).Positive := by
  intro s
  fin_cases s <;> simp [conc] <;> assumption

/-- Two explicit positive steady states are distinct. -/
theorem conc_ne {x₀ x₁ y₀ y₁ : ℝ} (h : x₀ ≠ y₀) : conc x₀ x₁ ≠ conc y₀ y₁ := by
  intro he
  have hxy := congrFun he (0 : Fin 2)
  have : x₀ = y₀ := by simpa [conc] using hxy
  exact h this

/-- **The eight multistationary networks of the family are multistationary.** -/
theorem multistationaryList_mem (b c d : Complex Sp2)
    (hN : (b, c, d) ∈ multistationaryList) :
    (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity := by
  have hN' : (b, c, d) ∈ multistationaryList := hN
  simp only [multistationaryList, List.mem_cons] at hN'
  rcases hN' with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases h1 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates1, conc 1 3, conc 2 2, conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_1.1, witness_1.2⟩
  · rcases h2 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates2, conc 1 5, conc 2 6, conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_2.1, witness_2.2⟩
  · rcases h3 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates3, conc 1 1, conc (17 / 2) (7 / 2), conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_3.1, witness_3.2⟩
  · rcases h4 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates4, conc 1 7, conc 2 10, conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_4.1, witness_4.2⟩
  · rcases h5 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates5, conc 2 5, conc 5 8, conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_5.1, witness_5.2⟩
  · rcases h6 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates6, conc 2 5, conc 5 8, conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_6.1, witness_6.2⟩
  · rcases h7 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates7, conc 1 3, conc 5 7, conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_7.1, witness_7.2⟩
  · rcases h8 with ⟨rfl, rfl, rfl⟩
    exact (twoRxnOpen_multistationary_iff _ _ _).mpr
      ⟨rates8, conc 1 4, conc 2 5, conc_pos (by norm_num) (by norm_num),
        conc_pos (by norm_num) (by norm_num), conc_ne (by norm_num), witness_8.1, witness_8.2⟩
  · exact absurd h9 (by simp)


/-- The one-reaction sum of the first reaction `X → b` is at most one: no bimolecular
one-reaction network is multistationary. -/
theorem first_sum_le_one (b : Complex Sp2) (hb : b ∈ bimolecular) :
    (∑ s ∈ (Finset.univ : Finset Sp2).filter (fun s => cX s < b s), cX s) ≤ 1 := by
  have hb' : b = Complex.zero ∨ b = cX ∨ b = cTwoX ∨ b = cY ∨ b = cTwoY ∨ b = cXY := by
    simpa [bimolecular] using hb
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The one-reaction sum of the second reaction `c → d` is at most one. -/
theorem second_sum_le_one (c d : Complex Sp2)
    (hc : c = cTwoX ∨ c = cXY ∨ c = cTwoY) (hd : d ∈ bimolecular) :
    (∑ s ∈ (Finset.univ : Finset Sp2).filter (fun s => c s < d s), c s) ≤ 1 := by
  have hd' : d = Complex.zero ∨ d = cX ∨ d = cTwoX ∨ d = cY ∨ d = cTwoY ∨ d = cXY := by
    simpa [bimolecular] using hd
  rcases hc with rfl | rfl | rfl <;> rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The eight multistationary networks of the family are atoms of multistationarity**, and
multistationary. -/
theorem multistationaryList_atom (b c d : Complex Sp2)
    (hN : (b, c, d) ∈ multistationaryList) :
    TwoRxnIsAtom cX b c d ∧
      (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity := by
  have hmulti : (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity :=
    multistationaryList_mem b c d hN
  have hN' : (b, c, d) ∈ multistationaryList := hN
  simp only [multistationaryList, List.mem_cons] at hN'
  rcases hN' with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases h1 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · rcases h2 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · rcases h3 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · rcases h4 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · rcases h5 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · rcases h6 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · rcases h7 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · rcases h8 with ⟨rfl, rfl, rfl⟩
    refine ⟨?_, hmulti⟩
    rw [twoRxnOpen_isAtom_iff]
    exact ⟨hmulti, by decide, by decide⟩
  · exact absurd h9 (by simp)


/-- **The atom members of the family** — the same eight networks: a bimolecular one-reaction
network is never multistationary, so a multistationary two-reaction network of the family is
automatically an atom. -/
def atomList : List (Complex Sp2 × Complex Sp2 × Complex Sp2) := multistationaryList

/-- **The classification table.**  The criterion of the module docstring selects exactly the eight
multistationary members of the family.  This is a finite computation over the seventy-five
members of the family and is discharged by the **kernel** `decide`. -/
theorem twoReaction_criterion_table :
    ∀ N ∈ twoReactionFamily, twoRxnMultistationary N.1 N.2.1 N.2.2 = true ↔ N ∈ multistationaryList := by
  decide

/-- **The atom table.** -/
theorem twoReaction_atom_table :
    ∀ N ∈ twoReactionFamily, (N ∈ atomList) ↔ twoRxnMultistationary N.1 N.2.1 N.2.2 = true := by
  decide

/-- The number of multistationary members of the family. -/
theorem multistationaryList_length : multistationaryList.length = 8 := by decide

/-- The number of atoms of the family. -/
theorem atomList_length : atomList.length = 8 := by decide


/-- **Soundness of the criterion.**  Whenever the criterion of the module docstring holds for a
member of the family, the network is multistationary (and, being bimolecular, an atom of
multistationarity). -/
theorem twoRxnMultistationary_sound (b c d : Complex Sp2) (hN : (b, c, d) ∈ twoReactionFamily)
    (h : twoRxnMultistationary b c d = true) :
    (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity ∧ TwoRxnIsAtom cX b c d := by
  refine ⟨multistationaryList_mem b c d ((twoReaction_criterion_table (b, c, d) hN).mp h), ?_⟩
  exact (multistationaryList_atom b c d ((twoReaction_criterion_table (b, c, d) hN).mp h)).1


/-! ### Necessary conditions for multistationarity -/

/-- **The elimination identity.**  For a steady state `x` of the canonical two-reaction network,
`v₀ l₁ x₁ = x₀ Q' + P'`, where `Q' = v₁ l₀ - κ₀ (v₁ u₀ - v₀ u₁)` and `P' = v₀ p₁ - v₁ p₀`.  This is
obtained by combining `v₁` times the first steady-state equation with `v₀` times the second one,
the monomial terms cancelling. -/
theorem twoRxnSteady_elim (b c d : Complex Sp2) (r : TwoRxnRates) (x : Concentration Sp2)
    (hx : TwoRxnSteady b c d r x) :
    ((d 0 : ℝ) - (c 0 : ℝ)) * r.l₁ * x 1
      = x 0 * (((d 1 : ℝ) - (c 1 : ℝ)) * r.l₀
          - r.κ₀ * (((d 1 : ℝ) - (c 1 : ℝ)) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - (c 0 : ℝ)) * (b 1 : ℝ)))
        + ((d 0 : ℝ) - (c 0 : ℝ)) * r.p₁ - ((d 1 : ℝ) - (c 1 : ℝ)) * r.p₀ := by
  have h0 := hx.1
  have h1 := hx.2
  ring_nf at h0 h1 ⊢
  linear_combination ((d 1 : ℝ) - (c 1 : ℝ)) * h0 - ((d 0 : ℝ) - (c 0 : ℝ)) * h1

/-- **A bimolecular complex has at most two molecules of any species.** -/
theorem bimolecular_le_two (y : Complex Sp2) (hy : y ∈ bimolecular) :
    (y 0 : ℝ) ≤ 2 ∧ (y 1 : ℝ) ≤ 2 := by
  have hy' : y = Complex.zero ∨ y = cX ∨ y = cTwoX ∨ y = cY ∨ y = cTwoY ∨ y = cXY := by
    simpa [bimolecular] using hy
  rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [cX, cTwoX, cY, cTwoY, cXY, Complex.zero]

/-- **`c = 2X` is never multistationary.**  The two first coordinates of the two steady states are
the two roots of `κ₁ v₀ t² - (l₀ - κ₀ u₀) t + p₀`; its constant term `p₀ > 0` would have to be
the product `κ₁ v₀ x₀ z₀ ≤ 0` of the two roots, a contradiction. -/
theorem not_multistationary_c_twoX (b c d : Complex Sp2) (hd : d ∈ bimolecular) (hc : c = cTwoX)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b c d r x) (hz : TwoRxnSteady b c d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) : False := by
  subst hc
  have hx0 := hx.1
  have hz0 := hz.1
  have hx1 := hx.2
  have hz1 := hz.2
  have hmonoX : (x 0) ^ (cTwoX 0) * (x 1) ^ (cTwoX 1) = x 0 * x 0 := by
    simp [cTwoX]
    ring
  have hmonoZ : (z 0) ^ (cTwoX 0) * (z 1) ^ (cTwoX 1) = z 0 * z 0 := by
    simp [cTwoX]
    ring
  rw [hmonoX] at hx0 hx1
  rw [hmonoZ] at hz0 hz1
  have hX0 : (cTwoX 0 : ℕ) = 2 := rfl
  have hd0 : (d 0 : ℝ) ≤ 2 := (bimolecular_le_two d hd).1
  set v0 : ℝ := (d 0 : ℝ) - (cTwoX 0 : ℝ) with hv0def
  set u0 : ℝ := (b 0 : ℝ) - 1 with hu0def
  have hqx : r.κ₁ * v0 * x 0 * x 0 - (r.l₀ - r.κ₀ * u0) * x 0 + r.p₀ = 0 := by
    linear_combination hx0
  have hqz : r.κ₁ * v0 * z 0 * z 0 - (r.l₀ - r.κ₀ * u0) * z 0 + r.p₀ = 0 := by
    linear_combination hz0
  have hv0 : v0 ≤ 0 := by
    have hX0R : (cTwoX 0 : ℝ) = 2 := by exact_mod_cast hX0
    have hv0' : v0 = (d 0 : ℝ) - 2 := by simp [hv0def, hX0R]
    linarith [hd0]
  by_cases hxz : x 0 = z 0
  · -- then the second coordinates agree as well, contradicting `x ≠ z`
    have hz1' : r.κ₀ * x 0 * ((b 1 : ℝ) - 0) + r.κ₁ * (x 0 * x 0) * ((d 1 : ℝ) - (cTwoX 1))
        + r.p₁ - r.l₁ * z 1 = 0 := by
      rw [← hxz] at hz1
      exact hz1
    have hlin : r.l₁ * z 1 - r.l₁ * x 1 = 0 := by
      ring_nf at hx1 hz1' ⊢
      linear_combination hx1 - hz1'
    have hne1 : r.l₁ ≠ 0 := by exact ne_of_gt r.pos.2.2.2.2.2
    have hxy : x 1 = z 1 := by
      have h2 : r.l₁ * x 1 = r.l₁ * z 1 := by linarith [hlin]
      exact mul_left_cancel₀ hne1 h2
    have hxyz : x = z := by
      funext s
      fin_cases s
      · exact hxz
      · exact hxy
    exact hne hxyz
  · -- the two roots are distinct, so the quadratic factors
    have hprod : (x 0 - z 0) * (r.κ₁ * v0 * (x 0 + z 0) - (r.l₀ - r.κ₀ * u0)) = 0 := by
      linear_combination hqx - hqz
    rcases mul_eq_zero.mp hprod with h | h
    · have hxz' : x 0 = z 0 := by linarith
      exact absurd hxz' hxz
    · have hp0 : r.p₀ = v0 * (r.κ₁ * x 0 * z 0) := by
        linear_combination hqx - x 0 * h
      generalize hprod : r.κ₁ * x 0 * z 0 = w at hp0
      have hw : 0 < w := by
        rw [← hprod]
        exact mul_pos (mul_pos r.pos.2.1 (hxp 0)) (hzp 0)
      nlinarith [hv0, hw, r.pos.2.2.1]

/-- **No member of the family whose second reaction has source `2X` is multistationary.** -/
theorem not_multistationary_of_c_twoX (b c d : Complex Sp2) (hc : c = cTwoX) (hd : d ∈ bimolecular) :
    ¬ (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity := by
  intro h
  obtain ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩ :=
    (twoRxnOpen_multistationary_iff b c d).mp h
  exact not_multistationary_c_twoX b c d hd hc r x z hxs hzs hxp hzp hne

end Network

end CRNT
