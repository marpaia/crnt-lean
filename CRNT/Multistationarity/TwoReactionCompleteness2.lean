import CRNT.Multistationarity.TwoReactionCompleteness

/-!
# The completeness of the two-reaction criterion: the sign conditions

This module discharges the **remaining** necessary conditions of the *completeness* argument for
the two-reaction classification of multistationarity carried out in
`CRNT.Multistationarity.TwoReactionClassification`, and thereby completes the criterion for
the two sub-families `c = X + Y` and `c = 2Y`.

## The setting

The setting is the one of Joshi and Shiu, *Atoms of multistationarity in chemical reaction
networks* (J. Math. Chem. **51** (2013), 153–178), restricted to the **two-species bimolecular
two-reaction fully open networks** of that paper: the two non-flow reactions are `X → b` and
`c → d`, where `b`, `c`, `d` are bimolecular complexes (at most two molecules each) on the two
species `X` (index `0`) and `Y` (index `1`).  The enumeration of the **75** members of this
family is `Network.twoReactionFamily` (`twoReactionFamily_card`), and the **closed-form
criterion** for multistationarity of such a network is the `Bool`-valued function

```
Network.twoRxnMultistationary : Complex Sp2 → Complex Sp2 → Complex Sp2 → Bool
```

which reads, with `u = b - X` and `v = d - c` the two reaction vectors and
`σ = v₁ u₀ - v₀ u₁`:

* `c = 2X`: the network is **never** multistationary;
* `c = X + Y`: the network is multistationary iff `v₀ ≠ 0` and either
  (`v₀ > 0` and `σ < 0` and `u₁ > 0`) or (`v₀ < 0`, `v₁ < 0` and `σ < 0`);
* `c = 2Y`: the network is multistationary iff `v₀ > 0`, `σ < 0` and `u₁ > 0`.

The criterion is derived from the **elimination identity** `twoRxnSteady_elim`

```
v₀ l₁ x₁ = x₀ Q' + P',   Q' = v₁ l₀ - κ₀ (v₁ u₀ - v₀ u₁),   P' = v₀ p₁ - v₁ p₀,
```

which holds at every steady state `x` of the canonical two-reaction network
`twoRxnOpen cX b c d` with rate constants `r = (κ₀, κ₁, p₀, p₁, l₀, l₁)`.

## What this module proves

The **completeness** of the criterion is the implication "the network is multistationary
⇒ the criterion holds".  Its content is *local to the sub-families*, because the source complex
`c` of the second reaction is one of `2X`, `X + Y`, `2Y`.

* The sub-family `c = 2X` is **already discharged** in the classification module, by
  `not_multistationary_of_c_twoX`: the two first coordinates of two steady states would be the
  two roots of `κ₁ v₀ t² - (l₀ - κ₀ u₀) t + p₀`, whose constant term `p₀ > 0` would have to
  be the product `κ₁ v₀ x₀ z₀ ≤ 0` of the two roots.

* The sub-family `c = X + Y` is discharged here by `twoRxn_multistationary_cXY_facts`, which
  proves the three missing necessary conditions in one go:

  * `twoRxn_multistationary_cXY_imp_sigma_neg` — the sign condition `σ < 0`;
  * `twoRxn_multistationary_cXY_imp_u1_pos` — the condition `u₁ > 0` in the branch `v₀ > 0`;
  * `twoRxn_multistationary_cXY_imp_v1_neg` — the condition `v₁ < 0` in the branch `v₀ < 0`.

* The sub-family `c = 2Y` is discharged here by `twoRxn_multistationary_cTwoY_imp_v0_pos`
  (the condition `v₀ > 0`) and `twoRxn_multistationary_cTwoY_imp_sigma_neg` (the sign condition
  `σ < 0`), the latter resting on the new intermediate statement
  `twoRxn_multistationary_cTwoY_imp_Q_pos` (the sign condition `Q' > 0`).

* The **payoff**: `twoRxnMultistationary_complete_cXY` and `twoRxnMultistationary_complete_cTwoY`
  prove that the criterion `Network.twoRxnMultistationary` holds for every multistationary
  network of the two sub-families.  Together with `not_multistationary_of_c_twoX` — which says
  that the twenty-five members with source `2X` are never multistationary, and for which the
  criterion is `false` by definition — this makes `Network.twoRxnMultistationary` an **exact
  characterisation** of multistationarity on all **seventy-five** members of the family: the
  twenty-five members with source `2X` are never multistationary, and on the remaining fifty
  (source `X + Y` or `2Y`) the criterion is `true` exactly for the multistationary networks.

## The discreteness argument

The sign conditions are driven by the **discreteness** of the complexes.  Because `b` and `d`
are *bimolecular* complexes, the coordinates of the reaction vectors take only very few values:
`u₀ = b 0 - 1 ∈ {-1, 0, 1}`, `u₁ = b 1 ∈ {0, 1, 2}`, `v₀ = d 0 - 1 ∈ {-1, 0, 1}` and
`v₁ = d 1 - 1 ∈ {-1, 0, 1}`.  In the sub-family `c = X + Y` the condition `v₀ ≠ 0` (proved in
`CRNT.Multistationarity.TwoReactionCompleteness`) leaves only six possibilities for `d`, and the
discreteness is what makes the sign conditions follow:

* `d = 0` or `d = 2X`: `v₁ = -1 ≤ 0`, so `Q' = v₁ l₀ - κ₀ σ > 0` gives `κ₀ σ < v₁ l₀ ≤ 0`,
  whence `σ < 0`;
* `d = 2X` (`v₀ = 1`): the first steady-state equation gives `l₀ - κ₀ u₀ > 0`, and
  `Q' = κ₀ (u₀ + u₁) - l₀ > 0` then gives `κ₀ u₁ > 0`, whence `u₁ > 0`;
* `d = Y` (`v₁ = 0`): then `σ = u₁ ≥ 0` contradicts `σ < 0`, so this case cannot occur;
* `d = 2Y` (`v₁ = 1`): the network is **never** multistationary
  (`not_multistationary_c_XplusY_d_twoY`), the positive steady state being unique.

In the sub-family `c = 2Y` the discreteness gives `v₁ = d 1 - 2 ∈ {-2, -1}` as soon as
`v₀ = d 0 > 0`, and `Q' > 0` then gives `σ < 0`.

## What is *not* proved here

* The **enumeration** of the *atom* table (`twoReaction_atom_table`) is *not* re-proved here;
  it is the finite, kernel-checked table of the classification module
  `CRNT.Multistationarity.TwoReactionClassification`, whose *completeness* for the two
  sub-families `c = X + Y` and `c = 2Y` is what this module establishes.
* The criterion is **not** claimed for complexes that are not bimolecular, nor for networks
  with more than two species, nor for the reversible two-reaction networks of the paper
  (which are outside the family `twoReactionFamily`).
* The closed-form criterion of `Network.twoRxnMultistationary` is *not* claimed to be a
  criterion for the *number* of positive steady states.

## Literature

* A. Joshi and W. Shiu, *Atoms of multistationarity in chemical reaction networks*,
  J. Math. Chem. **51** (2013), 153–178 — §6 enumerates the reversible bimolecular
  two-reaction networks; 35 of the 386 admit multiple positive mass-action steady states
  and the corresponding poset has 11 minimal elements.
* A. Joshi and W. Shiu, *A sharp bound on the number of equilibria of a two-reaction
  network* — the two-reaction case of the general bound.
-/

namespace CRNT

namespace Network

open scoped BigOperators

/-! ### Auxiliary lemmas -/

/-- **Vieta's formula for a quadratic.**  If `x` and `z` are two distinct real roots of
`a t ^ 2 + b * t + c`, then `a * x * z = c`. -/
lemma twoRxn_vieta {a b c x z : ℝ} (hx : a * x ^ 2 + b * x + c = 0)
    (hz : a * z ^ 2 + b * z + c = 0) (hne : x ≠ z) : a * x * z = c := by
  have hprod : (x - z) * (a * (x + z) + b) = 0 := by
    calc (x - z) * (a * (x + z) + b) = a * (x ^ 2 - z ^ 2) + b * (x - z) := by ring
    _ = 0 := by linear_combination hx - hz
  have hsum : a * (x + z) + b = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h (sub_ne_zero.mpr hne)
    · exact h
  have hsum' : a * (x + z) = -b := by linarith
  calc a * x * z = a * (x + z) * x - a * x ^ 2 := by ring
    _ = -b * x - a * x ^ 2 := by rw [hsum']
    _ = c := by nlinarith [hx]

/-- A bimolecular complex whose first coordinate is positive has at most one molecule of the
second species. -/
lemma bimolecular_d1_lt_two_of_d0_pos (d : Complex Sp2) (hd : d ∈ bimolecular)
    (h : 0 < (d 0 : ℝ)) : (d 1 : ℝ) < 2 := by
  have hd' : d = Complex.zero ∨ d = cX ∨ d = cTwoX ∨ d = cY ∨ d = cTwoY ∨ d = cXY := by
    simpa [bimolecular] using hd
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [Complex.zero] at h
  · norm_num [cX]
  · norm_num [cTwoX]
  · norm_num [cY] at h
  · norm_num [cTwoY] at h
  · norm_num [cXY]

/-- The cast of the integer first coordinate of the reaction vector `d - (X + Y)`. -/
lemma twoRxn_cast_v0 (d : Complex Sp2) : ((d 0 : ℤ) - 1 : ℝ) = (d 0 : ℝ) - 1 := by
  push_cast
  ring

/-- The cast of the integer second coordinate of the reaction vector `d - (X + Y)`. -/
lemma twoRxn_cast_v1 (d : Complex Sp2) : ((d 1 : ℤ) - 1 : ℝ) = (d 1 : ℝ) - 1 := by
  push_cast
  ring

/-- The cast of `σ = v₁ u₀ - v₀ u₁` for `c = X + Y`. -/
lemma twoRxn_cast_sigma (b d : Complex Sp2) :
    (sigmaVec b cXY d : ℝ)
      = ((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ) := by
  simp [sigmaVec, uVec, vVec, cXY]

/-- The cast of `σ = v₁ u₀ - v₀ u₁` for `c = 2Y`. -/
lemma twoRxn_cast_sigma_twoY (b d : Complex Sp2) :
    (sigmaVec b cTwoY d : ℝ)
      = ((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ) := by
  simp [sigmaVec, uVec, vVec, cTwoY]

/-- The integer cast of the first coordinate of the complex `X + Y`. -/
lemma twoRxn_cXY_cast_zero : (cXY 0 : ℤ) = 1 := rfl

/-- The integer cast of the second coordinate of the complex `X + Y`. -/
lemma twoRxn_cXY_cast_one : (cXY 1 : ℤ) = 1 := rfl

/-- The integer cast of the first coordinate of the complex `2Y`. -/
lemma twoRxn_cTwoY_cast_zero : (cTwoY 0 : ℤ) = 0 := rfl

/-- The integer cast of the second coordinate of the complex `2Y`. -/
lemma twoRxn_cTwoY_cast_one : (cTwoY 1 : ℤ) = 2 := rfl

/-! ### Passing the sign conditions from the reals to the integers -/

/-- The integer version of `v₀ < 0` for the reaction vector `d - (X + Y)`. -/
lemma twoRxn_int_v0_neg {d : Complex Sp2} (h : (d 0 : ℝ) - 1 < 0) : (d 0 : ℤ) - 1 < 0 := by
  have h' : d 0 = 0 := by
    have h2 : (d 0 : ℝ) < 1 := by linarith
    have h3 : d 0 < 1 := by exact_mod_cast h2
    omega
  omega

/-- The integer version of `v₀ > 0` for the reaction vector `d - (X + Y)`. -/
lemma twoRxn_int_v0_pos {d : Complex Sp2} (h : 0 < (d 0 : ℝ) - 1) : 0 < (d 0 : ℤ) - 1 := by
  have h2 : (d 0 : ℝ) > 1 := by linarith
  have h3 : 1 < d 0 := by exact_mod_cast h2
  omega

/-- The integer version of `v₁ < 0` for the reaction vector `d - (X + Y)`. -/
lemma twoRxn_int_v1_neg {d : Complex Sp2} (h : (d 1 : ℝ) - 1 < 0) : (d 1 : ℤ) - 1 < 0 := by
  have h' : d 1 = 0 := by
    have h2 : (d 1 : ℝ) < 1 := by linarith
    have h3 : d 1 < 1 := by exact_mod_cast h2
    omega
  omega

/-- The integer version of `v₀ ≠ 0` for the reaction vector `d - (X + Y)`. -/
lemma twoRxn_int_v0_ne {d : Complex Sp2} (h : (d 0 : ℝ) - 1 ≠ 0) : (d 0 : ℤ) - 1 ≠ 0 := by
  intro hh
  have hzero : (d 0 : ℝ) - 1 = 0 := by exact_mod_cast hh
  exact h hzero

/-- The integer version of `σ < 0` for the sub-family `c = X + Y`. -/
lemma twoRxn_int_sigma_neg {b d : Complex Sp2}
    (h : ((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ) < 0) :
    sigmaVec b cXY d < 0 := by
  have hcast := twoRxn_cast_sigma b d
  rw [← hcast] at h
  exact_mod_cast h

/-- The integer version of `σ < 0` for the sub-family `c = 2Y`. -/
lemma twoRxn_int_sigma_neg_twoY {b d : Complex Sp2}
    (h : ((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ) < 0) :
    sigmaVec b cTwoY d < 0 := by
  have hcast := twoRxn_cast_sigma_twoY b d
  rw [← hcast] at h
  exact_mod_cast h

/-- The integer version of `u₁ > 0`. -/
lemma twoRxn_int_u1_pos {b : Complex Sp2} (h : 0 < (b 1 : ℝ)) : 0 < (b 1 : ℤ) := by
  have h' : 0 < b 1 := by exact_mod_cast h
  omega

/-! ### The sub-family `c = X + Y` -/

/-- **The sub-family `c = X + Y` with `d = 2Y` is never multistationary.**  The first
steady-state equation determines `x₀` as a *decreasing* function of `x₁`, the second one
determines `x₁` as an *increasing* function of `x₀`; the positive steady state is therefore
unique.  Formally: eliminating `x₀` from the two equations gives a quadratic in `x₁` whose
constant term is negative, so it cannot have two distinct positive roots. -/
theorem not_multistationary_c_XplusY_d_twoY
    (b d : Complex Sp2) (hd : d ∈ bimolecular) (hd2 : d = cTwoY)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cXY d r x) (hz : TwoRxnSteady b cXY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) : False := by
  have hQ := twoRxn_multistationary_cXY_imp_Q_pos b d hd r x z hx hz hxp hzp hne
  subst hd2
  have hmonoX : (x 0) ^ (cXY 0) * (x 1) ^ (cXY 1) = x 0 * x 1 := by simp [cXY]
  have hmonoZ : (z 0) ^ (cXY 0) * (z 1) ^ (cXY 1) = z 0 * z 1 := by simp [cXY]
  have hx0 := hx.1
  have hx1 := hx.2
  have hz0 := hz.1
  have hz1 := hz.2
  rw [hmonoX] at hx0 hx1
  rw [hmonoZ] at hz0 hz1
  norm_num [cTwoY, cXY] at hx0 hx1 hz0 hz1 hQ
  -- `A = l₀ - κ₀ u₀` is positive, because `Q' = A - κ₀ u₁ > 0`
  have hA : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) := by
    have hQ' : 0 < r.l₀ - r.κ₀ * (((b 0 : ℝ) - 1) + (b 1 : ℝ)) := by linarith [hQ]
    have hnonneg : 0 ≤ r.κ₀ * (b 1 : ℝ) :=
      mul_nonneg r.pos.1.le (Nat.cast_nonneg _)
    linarith
  -- the two first-coordinate identities
  have hA_X : x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) = r.p₀ := by
    ring_nf at hx0 ⊢
    linarith [hx0]
  have hA_Z : z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * z 1) = r.p₀ := by
    ring_nf at hz0 ⊢
    linarith [hz0]
  -- the two second-coordinate identities
  have hB_X : x 0 * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * x 1) = r.l₁ * x 1 - r.p₁ := by
    ring_nf at hx1 ⊢
    linarith [hx1]
  have hB_Z : z 0 * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * z 1) = r.l₁ * z 1 - r.p₁ := by
    ring_nf at hz1 ⊢
    linarith [hz1]
  -- the two second coordinates are distinct
  have hx1z1 : x 1 ≠ z 1 := by
    intro h
    have hS : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1 := by
      have hmul : 0 < x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) := by
        rw [hA_X]
        exact r.pos.2.2.1
      rcases mul_pos_iff.mp hmul with h | h
      · exact h.2
      · exact absurd h.1 (not_lt_of_ge (hxp 0).le)
    have hprod : x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1)
        = z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) := by
      calc x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) = r.p₀ := hA_X
        _ = z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * z 1) := hA_Z.symm
        _ = z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) := by rw [h]
    have hx0z0 : x 0 = z 0 := by
      by_contra hc
      rcases lt_trichotomy (x 0) (z 0) with hlt | heq | hgt
      · have hlt' : x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1)
            < z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) :=
          mul_lt_mul_of_pos_right hlt hS
        linarith [hprod]
      · exact absurd heq hc
      · have hlt' : z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1)
            < x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) :=
          mul_lt_mul_of_pos_right hgt hS
        linarith [hprod]
    have hxyz : x = z := by
      funext s
      fin_cases s
      · exact hx0z0
      · exact h
    exact hne hxyz
  -- the quadratic satisfied by the second coordinate
  have hqX' : r.p₀ * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * x 1)
      - (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) * (r.l₁ * x 1 - r.p₁) = 0 := by
    have h1 : r.p₀ * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * x 1)
        = (r.κ₀ * (b 1 : ℝ) + r.κ₁ * x 1) * x 0
          * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) := by
      rw [← hA_X]
      ring
    have h2 : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) * (r.l₁ * x 1 - r.p₁)
        = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * x 1) * x 0
          * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * x 1) := by
      rw [← hB_X]
      ring
    rw [h1, h2]
    ring
  have hqX : r.κ₁ * r.l₁ * (x 1) ^ 2
      + ((r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.l₁ - r.κ₁ * (r.p₀ + r.p₁)) * x 1
      - ((r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ + r.p₀ * r.κ₀ * (b 1 : ℝ)) = 0 := by
    ring_nf at hqX' ⊢
    linarith [hqX']
  have hqZ' : r.p₀ * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * z 1)
      - (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * z 1) * (r.l₁ * z 1 - r.p₁) = 0 := by
    have h1 : r.p₀ * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * z 1)
        = (r.κ₀ * (b 1 : ℝ) + r.κ₁ * z 1) * z 0
          * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * z 1) := by
      rw [← hA_Z]
      ring
    have h2 : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * z 1) * (r.l₁ * z 1 - r.p₁)
        = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₁ * z 1) * z 0
          * (r.κ₀ * (b 1 : ℝ) + r.κ₁ * z 1) := by
      rw [← hB_Z]
      ring
    rw [h1, h2]
    ring
  have hqZ : r.κ₁ * r.l₁ * (z 1) ^ 2
      + ((r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.l₁ - r.κ₁ * (r.p₀ + r.p₁)) * z 1
      - ((r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ + r.p₀ * r.κ₀ * (b 1 : ℝ)) = 0 := by
    ring_nf at hqZ' ⊢
    linarith [hqZ']
  -- Vieta: the product of the two roots has the wrong sign
  have hvieta : r.κ₁ * r.l₁ * x 1 * z 1
      = -((r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ + r.p₀ * r.κ₀ * (b 1 : ℝ)) :=
    twoRxn_vieta hqX hqZ hx1z1
  have hpos : 0 < r.κ₁ * r.l₁ * x 1 * z 1 := by
    have h1 : 0 < r.κ₁ * r.l₁ := mul_pos r.pos.2.1 r.pos.2.2.2.2.2
    have h2 : 0 < x 1 * z 1 := mul_pos (hxp 1) (hzp 1)
    calc 0 < (r.κ₁ * r.l₁) * (x 1 * z 1) := mul_pos h1 h2
      _ = r.κ₁ * r.l₁ * x 1 * z 1 := by ring
  have hneg : -((r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ + r.p₀ * r.κ₀ * (b 1 : ℝ)) < 0 := by
    have h1 : 0 < (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ := mul_pos hA r.pos.2.2.2.1
    have h2 : 0 ≤ r.p₀ * r.κ₀ * (b 1 : ℝ) :=
      mul_nonneg (mul_nonneg r.pos.2.2.1.le r.pos.1.le) (Nat.cast_nonneg _)
    linarith
  linarith

/-- **The facts about a multistationary network of the sub-family `c = X + Y`.**  If the fully
open network `X → b`, `X + Y → d` is multistationary, then `v₀ ≠ 0`, `σ < 0`, and, according
to the sign of `v₀`, either `u₁ > 0` (if `v₀ > 0`) or `v₁ < 0` (if `v₀ < 0`). -/
theorem twoRxn_multistationary_cXY_facts
    (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cXY d r x) (hz : TwoRxnSteady b cXY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    (d 0 : ℝ) - 1 ≠ 0 ∧
    ((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ) < 0 ∧
    (0 < (d 0 : ℝ) - 1 → 0 < (b 1 : ℝ)) ∧
    ((d 0 : ℝ) - 1 < 0 → (d 1 : ℝ) - 1 < 0) := by
  have hQ := twoRxn_multistationary_cXY_imp_Q_pos b d hd r x z hx hz hxp hzp hne
  have hv0ne : (d 0 : ℝ) - 1 ≠ 0 := by
    intro h
    exact not_multistationary_of_c_XplusY_of_v0_zero b d hd h r x z hx hz hxp hzp hne
  have hd' : d = Complex.zero ∨ d = cX ∨ d = cTwoX ∨ d = cY ∨ d = cTwoY ∨ d = cXY := by
    simpa [bimolecular] using hd
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl
  · -- `d = 0`: `v₀ = -1`, `v₁ = -1`
    have hQ' : 0 < r.κ₀ * ((b 0 : ℝ) - 1 - (b 1 : ℝ)) := by
      have := hQ
      norm_num [Complex.zero] at this
      linarith [this, r.pos.2.2.2.2.1]
    have hw : 0 < (b 0 : ℝ) - 1 - (b 1 : ℝ) := by
      rcases mul_pos_iff.mp hQ' with h | h
      · exact h.2
      · exact absurd h.1 (not_lt_of_ge r.pos.1.le)
    have h1 : (Complex.zero 0 : ℝ) - 1 ≠ 0 := by norm_num [Complex.zero]
    have h2 : ((Complex.zero 1 : ℝ) - 1) * ((b 0 : ℝ) - 1)
        - ((Complex.zero 0 : ℝ) - 1) * (b 1 : ℝ) < 0 := by
      norm_num [Complex.zero]
      linarith [hw]
    have h3 : 0 < (Complex.zero 0 : ℝ) - 1 → 0 < (b 1 : ℝ) := by
      intro h
      norm_num [Complex.zero] at h
    have h4 : (Complex.zero 0 : ℝ) - 1 < 0 → (Complex.zero 1 : ℝ) - 1 < 0 := by
      intro _
      norm_num [Complex.zero]
    exact ⟨h1, h2, h3, h4⟩
  · -- `d = X`: `v₀ = 0`, impossible
    have hv0 : (cX 0 : ℝ) - 1 = 0 := by norm_num [cX]
    exact (hv0ne hv0).elim
  · -- `d = 2X`: `v₀ = 1`, `v₁ = -1`
    have hQ'' : r.κ₀ * ((b 0 : ℝ) - 1) + r.κ₀ * (b 1 : ℝ) > r.l₀ := by
      have := hQ
      norm_num [cTwoX] at this
      ring_nf at this ⊢
      linarith [this]
    -- `σ = -(u₀ + u₁) < 0`
    have hw : 0 < (b 0 : ℝ) - 1 + (b 1 : ℝ) := by
      have hmul : 0 < r.κ₀ * (((b 0 : ℝ) - 1) + (b 1 : ℝ)) := by
        have := hQ''
        ring_nf at this ⊢
        linarith [this, r.pos.2.2.2.2.1]
      rcases mul_pos_iff.mp hmul with h | h
      · exact h.2
      · exact absurd h.1 (not_lt_of_ge r.pos.1.le)
    -- the first steady-state equation forces `l₀ - κ₀ u₀ > 0`
    have hmonoX : (x 0) ^ (cXY 0) * (x 1) ^ (cXY 1) = x 0 * x 1 := by simp [cXY]
    have hx0 := hx.1
    rw [hmonoX] at hx0
    norm_num [cTwoX, cXY] at hx0
    have hAx : x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) - r.κ₁ * x 1) = r.p₀ := by
      ring_nf at hx0 ⊢
      linarith [hx0]
    have hApos : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) := by
      have hmul : 0 < x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) - r.κ₁ * x 1) := by
        rw [hAx]
        exact r.pos.2.2.1
      rcases mul_pos_iff.mp hmul with h | h
      · have h2 : 0 < r.κ₁ * x 1 := mul_pos r.pos.2.1 (hxp 1)
        linarith [h.2, h2]
      · exact absurd h.1 (not_lt_of_ge (hxp 0).le)
    -- `κ₀ u₁ > 0`
    have hmul : 0 < r.κ₀ * (b 1 : ℝ) := by
      have h1 : r.κ₀ * ((b 0 : ℝ) - 1) < r.l₀ := by linarith [hApos]
      linarith [h1, hQ'']
    have hu1 : 0 < (b 1 : ℝ) := by
      rcases mul_pos_iff.mp hmul with h | h
      · exact h.2
      · exact absurd h.1 (not_lt_of_ge r.pos.1.le)
    have h1 : (cTwoX 0 : ℝ) - 1 ≠ 0 := by norm_num [cTwoX]
    have h2 : ((cTwoX 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((cTwoX 0 : ℝ) - 1) * (b 1 : ℝ) < 0 := by
      norm_num [cTwoX]
      linarith [hw]
    have h3 : 0 < (cTwoX 0 : ℝ) - 1 → 0 < (b 1 : ℝ) := fun _ => hu1
    have h4 : (cTwoX 0 : ℝ) - 1 < 0 → (cTwoX 1 : ℝ) - 1 < 0 := by
      intro h
      norm_num [cTwoX] at h
    exact ⟨h1, h2, h3, h4⟩
  · -- `d = Y`: `v₀ = -1`, `v₁ = 0`, impossible
    have hQ' : 0 < -(r.κ₀ * (b 1 : ℝ)) := by
      have := hQ
      norm_num [cY] at this
      linarith [this]
    have hneg : r.κ₀ * (b 1 : ℝ) < 0 := by linarith [hQ']
    have hnonneg : 0 ≤ r.κ₀ * (b 1 : ℝ) :=
      mul_nonneg r.pos.1.le (Nat.cast_nonneg _)
    linarith
  · -- `d = 2Y`: `v₀ = -1`, `v₁ = 1`, impossible
    exact (not_multistationary_c_XplusY_d_twoY b cTwoY hd rfl r x z hx hz hxp hzp hne).elim
  · -- `d = X + Y`: `v₀ = 0`, impossible
    have hv0 : (cXY 0 : ℝ) - 1 = 0 := by norm_num [cXY]
    exact (hv0ne hv0).elim

/-- **Necessary condition for the sub-family `c = X + Y`: the sign condition `σ < 0`.**  With
`Q' = v₁ l₀ - κ₀ (v₁ u₀ - v₀ u₁) > 0` and `v₁ ≤ 0` one gets `κ₀ σ < v₁ l₀ ≤ 0`, hence `σ < 0`. -/
theorem twoRxn_multistationary_cXY_imp_sigma_neg
    (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cXY d r x) (hz : TwoRxnSteady b cXY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    ((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ) < 0 :=
  (twoRxn_multistationary_cXY_facts b d hd r x z hx hz hxp hzp hne).2.1

/-- **Necessary condition for the sub-family `c = X + Y`: `u₁ > 0`.**  For `v₀ = 1`, `v₁ = -1`
one has `Q' = κ₀ (u₀ + u₁) - l₀ > 0` together with `l₀ - κ₀ u₀ > 0`, giving `u₁ > 0`. -/
theorem twoRxn_multistationary_cXY_imp_u1_pos
    (b d : Complex Sp2) (hd : d ∈ bimolecular) (hv0 : 0 < (d 0 : ℝ) - 1)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cXY d r x) (hz : TwoRxnSteady b cXY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    0 < (b 1 : ℝ) :=
  (twoRxn_multistationary_cXY_facts b d hd r x z hx hz hxp hzp hne).2.2.1 hv0

/-- **Necessary condition for the sub-family `c = X + Y`: `v₁ < 0` when `v₀ < 0`.**  The value
`v₁ = 0` would force `σ = u₁ ≥ 0`, contradicting the sign condition. -/
theorem twoRxn_multistationary_cXY_imp_v1_neg
    (b d : Complex Sp2) (hd : d ∈ bimolecular) (hv0 : (d 0 : ℝ) - 1 < 0)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cXY d r x) (hz : TwoRxnSteady b cXY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    (d 1 : ℝ) - 1 < 0 :=
  (twoRxn_multistationary_cXY_facts b d hd r x z hx hz hxp hzp hne).2.2.2 hv0

/-! ### The sub-family `c = 2Y` -/

/-- **Necessary condition for the sub-family `c = 2Y`: the second reaction must consume `X`.**
If the second reaction `2Y → d` does not change the number of `X` molecules (`d 0 = 0`), then the
first steady-state equation determines `x₀` and the second one is a quadratic in `x₁` alone
which is strictly decreasing on the positive half-line; the positive steady state is unique and
the network is not multistationary.  The criterion `Network.twoRxnMultistationary` requires
`v₀ > 0` in this sub-family. -/
theorem twoRxn_multistationary_cTwoY_imp_v0_pos
    (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cTwoY d r x) (hz : TwoRxnSteady b cTwoY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    0 < (d 0 : ℝ) := by
  by_contra h
  have hd0 : (d 0 : ℝ) = 0 := by
    have hnonneg : 0 ≤ (d 0 : ℝ) := Nat.cast_nonneg _
    linarith
  have hd1 : (d 1 : ℝ) ≤ 2 := (bimolecular_le_two d hd).2
  have hmonoX : (x 0) ^ (cTwoY 0) * (x 1) ^ (cTwoY 1) = x 1 * x 1 := by
    simp [cTwoY]
    ring
  have hmonoZ : (z 0) ^ (cTwoY 0) * (z 1) ^ (cTwoY 1) = z 1 * z 1 := by
    simp [cTwoY]
    ring
  have hx0 := hx.1
  have hx1 := hx.2
  have hz0 := hz.1
  have hz1 := hz.2
  rw [hmonoX] at hx0 hx1
  rw [hmonoZ] at hz0 hz1
  rw [hd0] at hx0 hz0
  norm_num [cTwoY] at hx0 hx1 hz0 hz1
  -- the first equation determines `x 0`
  have hA_X : x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) = r.p₀ := by
    ring_nf at hx0 ⊢
    linarith [hx0]
  have hA_Z : z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) = r.p₀ := by
    ring_nf at hz0 ⊢
    linarith [hz0]
  have hA : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) := by
    have hmul : 0 < x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) := by
      rw [hA_X]
      exact r.pos.2.2.1
    rcases mul_pos_iff.mp hmul with h | h
    · exact h.2
    · exact absurd h.1 (not_lt_of_ge (hxp 0).le)
  have hx0z0 : x 0 = z 0 := by
    have h1 : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0
        = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0 := by
      calc (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0 = r.p₀ := by rw [← hA_X]; ring
        _ = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0 := by rw [← hA_Z]; ring
    exact mul_left_cancel₀ hA.ne' h1
  -- the second equation then determines `x 1`
  have hdiff : (x 1 - z 1) * (r.κ₁ * ((d 1 : ℝ) - 2) * (x 1 + z 1) - r.l₁) = 0 := by
    have hz1' : r.κ₀ * x 0 * (b 1 : ℝ) + r.κ₁ * (z 1 * z 1) * ((d 1 : ℝ) - 2)
        + r.p₁ - r.l₁ * z 1 = 0 := by
      rw [← hx0z0] at hz1
      exact hz1
    ring_nf at hx1 hz1' ⊢
    linarith [hx1, hz1']
  have hbr : r.κ₁ * ((d 1 : ℝ) - 2) * (x 1 + z 1) - r.l₁ ≠ 0 := by
    have hsum : 0 < x 1 + z 1 := by linarith [hxp 1, hzp 1]
    have hneg : (d 1 : ℝ) - 2 ≤ 0 := by linarith [hd1]
    have hmul : r.κ₁ * ((d 1 : ℝ) - 2) * (x 1 + z 1) ≤ 0 := by
      have h2 : r.κ₁ * ((d 1 : ℝ) - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos r.pos.2.1.le hneg
      exact mul_nonpos_of_nonpos_of_nonneg h2 hsum.le
    have hlt : r.κ₁ * ((d 1 : ℝ) - 2) * (x 1 + z 1) - r.l₁ < 0 := by
      linarith [hmul, r.pos.2.2.2.2.2]
    exact ne_of_lt hlt
  have hx1z1 : x 1 = z 1 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hbr
  have hxyz : x = z := by
    funext s
    fin_cases s
    · exact hx0z0
    · exact hx1z1
  exact hne hxyz

/-- **Necessary condition for the sub-family `c = 2Y`: the sign condition `Q' > 0`.**  The two
second coordinates are the two roots of a quadratic whose constant term is positive, so its
leading coefficient `κ₁ Q'` is positive. -/
theorem twoRxn_multistationary_cTwoY_imp_Q_pos
    (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cTwoY d r x) (hz : TwoRxnSteady b cTwoY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    0 < ((d 1 : ℝ) - 2) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ)) := by
  have hv0pos : 0 < (d 0 : ℝ) :=
    twoRxn_multistationary_cTwoY_imp_v0_pos b d hd r x z hx hz hxp hzp hne
  have hmonoX : (x 0) ^ (cTwoY 0) * (x 1) ^ (cTwoY 1) = x 1 * x 1 := by
    simp [cTwoY]
    ring
  have hmonoZ : (z 0) ^ (cTwoY 0) * (z 1) ^ (cTwoY 1) = z 1 * z 1 := by
    simp [cTwoY]
    ring
  have hx0 := hx.1
  have hx1 := hx.2
  have hz0 := hz.1
  have hz1 := hz.2
  rw [hmonoX] at hx0 hx1
  rw [hmonoZ] at hz0 hz1
  norm_num [cTwoY] at hx0 hx1 hz0 hz1
  -- `A = l₀ - κ₀ u₀` is positive
  have hA_X : x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
      = r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) + r.p₀ := by
    ring_nf at hx0 ⊢
    linarith [hx0]
  have hA_Z : z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
      = r.κ₁ * (d 0 : ℝ) * (z 1 * z 1) + r.p₀ := by
    ring_nf at hz0 ⊢
    linarith [hz0]
  have hA : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) := by
    have hmul : 0 < x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) := by
      rw [hA_X]
      have h1 : 0 ≤ r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) :=
        mul_nonneg (mul_nonneg r.pos.2.1.le (Nat.cast_nonneg _)) (mul_self_nonneg _)
      linarith [h1, r.pos.2.2.1]
    rcases mul_pos_iff.mp hmul with h | h
    · exact h.2
    · exact absurd h.1 (not_lt_of_ge (hxp 0).le)
  -- the second coordinates are distinct
  have hx1z1 : x 1 ≠ z 1 := by
    intro h
    have hprod : x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
        = z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) := by
      calc x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
          = r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) + r.p₀ := hA_X
        _ = r.κ₁ * (d 0 : ℝ) * (z 1 * z 1) + r.p₀ := by rw [h]
        _ = z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) := hA_Z.symm
    have hx0z0 : x 0 = z 0 := mul_right_cancel₀ hA.ne' hprod
    have hxyz : x = z := by
      funext s
      fin_cases s
      · exact hx0z0
      · exact h
    exact hne hxyz
  -- the two second-coordinate identities
  have hB_X : r.κ₀ * x 0 * (b 1 : ℝ)
      = r.l₁ * x 1 - r.κ₁ * ((d 1 : ℝ) - 2) * (x 1 * x 1) - r.p₁ := by
    ring_nf at hx1 ⊢
    linarith [hx1]
  have hB_Z : r.κ₀ * z 0 * (b 1 : ℝ)
      = r.l₁ * z 1 - r.κ₁ * ((d 1 : ℝ) - 2) * (z 1 * z 1) - r.p₁ := by
    ring_nf at hz1 ⊢
    linarith [hz1]
  -- the quadratic satisfied by the second coordinate
  have hqX' : r.κ₀ * (b 1 : ℝ) * (r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) + r.p₀)
      = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
        * (r.l₁ * x 1 - r.κ₁ * ((d 1 : ℝ) - 2) * (x 1 * x 1) - r.p₁) := by
    have h1 : r.κ₀ * (b 1 : ℝ) * (r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) + r.p₀)
        = r.κ₀ * (b 1 : ℝ) * x 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) := by
      rw [← hA_X]
      ring
    have h2 : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
        * (r.l₁ * x 1 - r.κ₁ * ((d 1 : ℝ) - 2) * (x 1 * x 1) - r.p₁)
        = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.κ₀ * x 0 * (b 1 : ℝ) := by
      rw [← hB_X]
      ring
    rw [h1, h2]
    ring
  have hqX : r.κ₁ * (((d 1 : ℝ) - 2) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ))) * (x 1) ^ 2
      + (-(r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.l₁) * x 1
      + (r.κ₀ * (b 1 : ℝ) * r.p₀ + (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁) = 0 := by
    ring_nf at hqX' ⊢
    linarith [hqX']
  have hqZ' : r.κ₀ * (b 1 : ℝ) * (r.κ₁ * (d 0 : ℝ) * (z 1 * z 1) + r.p₀)
      = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
        * (r.l₁ * z 1 - r.κ₁ * ((d 1 : ℝ) - 2) * (z 1 * z 1) - r.p₁) := by
    have h1 : r.κ₀ * (b 1 : ℝ) * (r.κ₁ * (d 0 : ℝ) * (z 1 * z 1) + r.p₀)
        = r.κ₀ * (b 1 : ℝ) * z 0 * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) := by
      rw [← hA_Z]
      ring
    have h2 : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))
        * (r.l₁ * z 1 - r.κ₁ * ((d 1 : ℝ) - 2) * (z 1 * z 1) - r.p₁)
        = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.κ₀ * z 0 * (b 1 : ℝ) := by
      rw [← hB_Z]
      ring
    rw [h1, h2]
    ring
  have hqZ : r.κ₁ * (((d 1 : ℝ) - 2) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ))) * (z 1) ^ 2
      + (-(r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.l₁) * z 1
      + (r.κ₀ * (b 1 : ℝ) * r.p₀ + (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁) = 0 := by
    ring_nf at hqZ' ⊢
    linarith [hqZ']
  -- Vieta: `Q' > 0`
  have hvieta : r.κ₁ * (((d 1 : ℝ) - 2) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ))) * x 1 * z 1
      = r.κ₀ * (b 1 : ℝ) * r.p₀ + (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ :=
    twoRxn_vieta hqX hqZ hx1z1
  have hpos : 0 < r.κ₀ * (b 1 : ℝ) * r.p₀
      + (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ := by
    have h1 : 0 < (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * r.p₁ := mul_pos hA r.pos.2.2.2.1
    have h2 : 0 ≤ r.κ₀ * (b 1 : ℝ) * r.p₀ :=
      mul_nonneg (mul_nonneg r.pos.1.le (Nat.cast_nonneg _)) r.pos.2.2.1.le
    linarith
  have hmul : 0 < r.κ₁ * (((d 1 : ℝ) - 2) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ))) * x 1 * z 1 := by
    rw [hvieta]
    exact hpos
  have hleft : 0 < r.κ₁ * x 1 * z 1 := by
    have h1 : 0 < r.κ₁ := r.pos.2.1
    have h2 : 0 < x 1 * z 1 := mul_pos (hxp 1) (hzp 1)
    calc 0 < r.κ₁ * (x 1 * z 1) := mul_pos h1 h2
      _ = r.κ₁ * x 1 * z 1 := by ring
  have hmul' : 0 < (r.κ₁ * x 1 * z 1)
      * (((d 1 : ℝ) - 2) * r.l₀
        - r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ))) := by
    have h := hmul
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hQ : 0 < ((d 1 : ℝ) - 2) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ)) := by
    rcases mul_pos_iff.mp hmul' with h | h
    · exact h.2
    · exact absurd h.1 (not_lt_of_ge hleft.le)
  exact hQ

/-- **Necessary condition for the sub-family `c = 2Y`: the sign condition `σ < 0`.**  Here
`Q' = v₁ l₀ - κ₀ (v₁ u₀ - v₀ u₁) > 0` and `v₁ < 0`, so `κ₀ σ < v₁ l₀ < 0`. -/
theorem twoRxn_multistationary_cTwoY_imp_sigma_neg
    (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cTwoY d r x) (hz : TwoRxnSteady b cTwoY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    ((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ) < 0 := by
  have hQ := twoRxn_multistationary_cTwoY_imp_Q_pos b d hd r x z hx hz hxp hzp hne
  have hv0pos : 0 < (d 0 : ℝ) :=
    twoRxn_multistationary_cTwoY_imp_v0_pos b d hd r x z hx hz hxp hzp hne
  have hd1lt : (d 1 : ℝ) < 2 := bimolecular_d1_lt_two_of_d0_pos d hd hv0pos
  have hv1neg : (d 1 : ℝ) - 2 < 0 := by linarith [hd1lt]
  have h1 : r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ))
      < ((d 1 : ℝ) - 2) * r.l₀ := by
    linarith [hQ]
  have h2 : ((d 1 : ℝ) - 2) * r.l₀ < 0 := mul_neg_of_neg_of_pos hv1neg r.pos.2.2.2.2.1
  have h3 : r.κ₀ * (((d 1 : ℝ) - 2) * ((b 0 : ℝ) - 1) - (d 0 : ℝ) * (b 1 : ℝ)) < 0 := by
    linarith [h1, h2]
  rcases mul_neg_iff.mp h3 with h | h
  · exact h.2
  · exact absurd h.1 (not_lt_of_ge r.pos.1.le)

/-! ### The completeness of the criterion -/

/-- **Completeness of the two-reaction criterion for the sub-family `c = X + Y`.**  If the fully
open network `X → b`, `X + Y → d` is multistationary, then the criterion
`twoRxnMultistationary b cXY d` holds. -/
theorem twoRxnMultistationary_complete_cXY (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (h : (twoRxnOpen cX b cXY d).fullyOpen.HasMultistationarityCapacity) :
    twoRxnMultistationary b cXY d = true := by
  obtain ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩ :=
    (twoRxnOpen_multistationary_iff b cXY d).mp h
  have hfacts := twoRxn_multistationary_cXY_facts b d hd r x z hxs hzs hxp hzp hne
  have hv0ne : (d 0 : ℤ) - 1 ≠ 0 := twoRxn_int_v0_ne hfacts.1
  have hσ : sigmaVec b cXY d < 0 := twoRxn_int_sigma_neg hfacts.2.1
  have hσ' : ((d 1 : ℤ) - 1) * ((b 0 : ℤ) - 1) - ((d 0 : ℤ) - 1) * (b 1 : ℤ) < 0 := by
    simpa only [sigmaVec, uVec, vVec, twoRxn_cXY_cast_zero, twoRxn_cXY_cast_one] using hσ
  simp only [twoRxnMultistationary, uVec, vVec, sigmaVec]
  norm_num [cXY]
  refine ⟨?_, ?_, ?_⟩
  · decide
  · exact hv0ne
  · split
    · -- the branch `v₀ < 0`
      have hv0lt : (d 0 : ℝ) - 1 < 0 := by
        have hzero : (d 0 : ℝ) = 0 := by exact_mod_cast ‹d 0 = 0›
        linarith
      have hv1negℝ : (d 1 : ℝ) - 1 < 0 := hfacts.2.2.2 hv0lt
      have hv1neg : (d 1 : ℤ) - 1 < 0 := twoRxn_int_v1_neg hv1negℝ
      have hd1 : d 1 = 0 := by omega
      refine ⟨hd1, lt_of_sub_neg hσ'⟩
    · -- the branch `v₀ > 0`
      have hv0gt : 0 < (d 0 : ℝ) - 1 := by
        have hne : 0 < d 0 := by omega
        have hge : 1 ≤ (d 0 : ℝ) := by exact_mod_cast hne
        have hne' : (d 0 : ℝ) - 1 ≠ 0 := hfacts.1
        exact lt_of_le_of_ne (by linarith) (Ne.symm hne')
      have hu1ℝ : 0 < (b 1 : ℝ) := hfacts.2.2.1 hv0gt
      have hu1 : 0 < b 1 := by exact_mod_cast hu1ℝ
      exact ⟨lt_of_sub_neg hσ', hu1⟩

/-- **Completeness of the two-reaction criterion for the sub-family `c = 2Y`.**  If the fully
open network `X → b`, `2Y → d` is multistationary, then the criterion
`twoRxnMultistationary b cTwoY d` holds. -/
theorem twoRxnMultistationary_complete_cTwoY (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (h : (twoRxnOpen cX b cTwoY d).fullyOpen.HasMultistationarityCapacity) :
    twoRxnMultistationary b cTwoY d = true := by
  obtain ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩ :=
    (twoRxnOpen_multistationary_iff b cTwoY d).mp h
  have hv0pos : 0 < (d 0 : ℝ) :=
    twoRxn_multistationary_cTwoY_imp_v0_pos b d hd r x z hxs hzs hxp hzp hne
  have hσ : sigmaVec b cTwoY d < 0 :=
    twoRxn_int_sigma_neg_twoY
      (twoRxn_multistationary_cTwoY_imp_sigma_neg b d hd r x z hxs hzs hxp hzp hne)
  have hσ' : ((d 1 : ℤ) - 2) * ((b 0 : ℤ) - 1) - (d 0 : ℤ) * (b 1 : ℤ) < 0 := by
    simpa only [sigmaVec, uVec, vVec, twoRxn_cTwoY_cast_zero, twoRxn_cTwoY_cast_one,
      Int.sub_zero] using hσ
  have hb1 : b 1 ≠ 0 := by
    intro hh
    have hzero : (b 1 : ℝ) = 0 := by simp [hh]
    exact not_multistationary_of_c_twoY_of_b1_zero b d hd hzero r x z hxs hzs hxp hzp hne
  simp only [twoRxnMultistationary, uVec, vVec, sigmaVec]
  norm_num [cTwoY]
  refine ⟨?_, ?_⟩
  · decide
  · split
    · exact absurd ‹![0, 2] = cXY› (by decide)
    · have hv0 : 0 < d 0 := by exact_mod_cast hv0pos
      have hu1 : 0 < b 1 := by omega
      exact ⟨⟨hv0, lt_of_sub_neg hσ'⟩, hu1⟩

/-- **A non-vacuity check for `twoRxnMultistationary_complete_cXY`.**  The multistationary member
`X → 2X`, `X + Y → 0` of the family (with the explicit witness `witness_1`) is an instance of the
completeness theorem, and the criterion indeed holds for it. -/
theorem twoRxnMultistationary_complete_cXY_witness :
    twoRxnMultistationary cTwoX cXY Complex.zero = true := by
  rw [twoRxnMultistationary_complete_cXY cTwoX Complex.zero (by decide)
    (multistationaryList_mem cTwoX cXY Complex.zero (by simp [multistationaryList]))]

/-- **A non-vacuity check for `twoRxnMultistationary_complete_cTwoY`.**  The multistationary member
`X → 2Y`, `2Y → 2X` of the family (with the explicit witness `witness_3`) is an instance of the
completeness theorem, and the criterion indeed holds for it. -/
theorem twoRxnMultistationary_complete_cTwoY_witness :
    twoRxnMultistationary cTwoY cTwoY cTwoX = true := by
  rw [twoRxnMultistationary_complete_cTwoY cTwoY cTwoX (by decide)
    (multistationaryList_mem cTwoY cTwoY cTwoX (by simp [multistationaryList]))]

#print axioms twoRxn_multistationary_cXY_imp_sigma_neg
#print axioms twoRxn_multistationary_cXY_imp_u1_pos
#print axioms twoRxn_multistationary_cXY_imp_v1_neg
#print axioms twoRxn_multistationary_cTwoY_imp_v0_pos
#print axioms twoRxn_multistationary_cTwoY_imp_Q_pos
#print axioms twoRxn_multistationary_cTwoY_imp_sigma_neg
#print axioms twoRxnMultistationary_complete_cXY
#print axioms twoRxnMultistationary_complete_cTwoY

end Network

end CRNT
