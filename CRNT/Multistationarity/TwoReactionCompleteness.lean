import CRNT.Multistationarity.TwoReactionClassification

/-!
# Necessary conditions for the completeness of the two-reaction criterion

This module contributes the **analytic part** of the *completeness* argument for the
two-reaction classification of multistationarity carried out in
`CRNT.Multistationarity.TwoReactionClassification`.

## The setting

The setting is the one of Joshi and Shiu, *A sharp bound on the number of equilibria of a
two-reaction network* / *Atoms of multistationarity in chemical reaction networks*
(J. Math. Chem. **51** (2013), 153–178), restricted to the **two-species bimolecular
two-reaction fully open networks** of that paper: the two non-flow reactions are
`X → b` and `c → d`, where `b`, `c`, `d` are bimolecular complexes (at most two
molecules each) on the two species `X` (index `0`) and `Y` (index `1`).  The
enumeration of the **75** members of this family is `twoReactionFamily`
(`twoReactionFamily_card`), and the **closed-form criterion** for multistationarity of
such a network is the `Bool`-valued function

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
⇒ the criterion holds".  Its content is *local to the sub-families*, because the source
complex `c` of the second reaction is one of `2X`, `X + Y`, `2Y`.

* The sub-family `c = 2X` is **already discharged** in the classification module, by
  `not_multistationary_of_c_twoX`: the two first coordinates of two steady states would
  be the two roots of `κ₁ v₀ t² - (l₀ - κ₀ u₀) t + p₀`, whose constant term `p₀ > 0`
  would have to be the product `κ₁ v₀ x₀ z₀ ≤ 0` of the two roots.

* This module discharges the **two remaining sub-families** by refuting multistationarity
  under the failure of one of the conditions of the criterion:

  - `not_multistationary_of_c_XplusY_of_v0_zero` — the sub-family `c = X + Y`: if
    `v₀ = (d 0 : ℝ) - 1 = 0`, i.e. the second reaction does not change the number of `X`
    molecules, then the first steady-state equation `(l₀ - κ₀ u₀) x₀ = p₀` determines `x₀`
    and the second one then determines `x₁`; the positive steady state is unique and the
    network is not multistationary.  The criterion requires `v₀ ≠ 0` in this sub-family.

  - `not_multistationary_of_c_twoY_of_b1_zero` — the sub-family `c = 2Y`: if the first
    reaction `X → b` does not produce `Y` (`b 1 = 0`), then the second steady-state
    equation is the *quadratic* `κ₁ (d₁ - 2) x₁² - l₁ x₁ + p₁ = 0` in `x₁` alone, whose
    leading coefficient `d₁ - 2 ≤ 0` makes it strictly decreasing on the positive
    half-line; the positive steady state is unique and the network is not
    multistationary.  The criterion requires `u₁ = b 1 > 0` in this sub-family.

  - `twoRxn_multistationary_cXY_imp_Q_pos` — the sub-family `c = X + Y`: the sign
    condition `Q' > 0`.  With `Q' = v₁ l₀ - κ₀ (v₁ u₀ - v₀ u₁)`, the elimination identity
    `v₀ l₁ x₁ = x₀ Q' + P'` applied to the two steady states, together with the first
    steady-state equation, shows that the two first coordinates are the two roots of the
    quadratic

    ```
    κ₁ Q' t² + (κ₁ P' - l₁ (l₀ - κ₀ u₀)) t + l₁ p₀ = 0,
    ```

    whose constant term `l₁ p₀ > 0` and whose two roots `x₀, z₀` are positive force
    `κ₁ Q' x₀ z₀ = l₁ p₀`, i.e. `Q' > 0`.

## What is *not* proved here

This module does **not** prove the completeness of the criterion for the remaining
sub-families.  Writing out what the criterion demands in the two sub-families that are
touched here:

* for `c = X + Y` the criterion demands `v₀ ≠ 0` and, according to the sign of `v₀`,
  either (`v₀ > 0` and `σ < 0` and `u₁ > 0`) or (`v₀ < 0` and `v₁ < 0` and `σ < 0`);
  this module proves `v₀ ≠ 0` (from `not_multistationary_of_c_XplusY_of_v0_zero`) and the
  sign condition `Q' > 0` (from `twoRxn_multistationary_cXY_imp_Q_pos`), but **not**
  `σ < 0`, **not** `u₁ > 0` and **not** `v₁ < 0`;
* for `c = 2Y` the criterion demands `v₀ > 0`, `σ < 0` and `u₁ > 0`; this module proves
  the necessary condition `u₁ > 0` (from `not_multistationary_of_c_twoY_of_b1_zero`), but
  **not** `v₀ > 0` and **not** `σ < 0`.

The two missing conditions of the sub-family `c = X + Y` do follow from `Q' > 0` *if* one
also uses the **discreteness** of the complexes `b` and `d` (the values
`u₀ = b 0 - 1 ∈ {-1, 0, 1}`, `u₁ = b 1 ∈ {0, 1, 2}`, `v₀ = d 0 - 1 ∈ {-1, 0, 1}`,
`v₁ = d 1 - 1 ∈ {-1, 0, 1}`, together with `d 0 = 0` or `2` in the two branches of the
criterion): for `v₀ > 0` one has `v₁ ≤ 0`, whence `σ < 0` follows from
`Q' = v₁ l₀ - κ₀ σ > 0`; for `v₀ < 0` one has `v₁ ≤ 0` as well, whence `σ < 0` again, and
`v₁ = 0` is excluded because it would force `σ = u₁ ≥ 0`.  This last argument is **not**
formalised here.

The **completeness** of the criterion (the implication "multistationary ⇒ the criterion
holds") therefore **remains the outstanding item of leaf M11** of `docs/field-map.md`,
exactly as it was left by `CRNT.Multistationarity.TwoReactionClassification`.

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

/-- **Necessary condition for the sub-family `c = 2Y`: the first reaction must produce `Y`.**
If the second reaction has source `2Y` and the first reaction `X → b` does not produce `Y`
(`b 1 = 0`), then the network has at most one positive steady state, hence it is not
multistationary.  The criterion `Network.twoRxnMultistationary` requires `u₁ > 0`, i.e. exactly
`b 1 > 0`. -/
theorem not_multistationary_of_c_twoY_of_b1_zero
    (b d : Complex Sp2) (hd : d ∈ bimolecular) (hb1 : (b 1 : ℝ) = 0)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cTwoY d r x) (hz : TwoRxnSteady b cTwoY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) : False := by
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
  have hY1 : (cTwoY 1 : ℝ) = 2 := by norm_num [cTwoY]
  have hY0 : (cTwoY 0 : ℝ) = 0 := by norm_num [cTwoY]
  simp only [hY0, hY1] at hx0 hx1 hz0 hz1
  rw [hb1] at hx1 hz1
  -- the second steady-state equations, in `x 1` alone
  have hx1' : r.κ₁ * (x 1 * x 1) * ((d 1 : ℝ) - 2) + r.p₁ - r.l₁ * x 1 = 0 := by
    linarith [hx1]
  have hz1' : r.κ₁ * (z 1 * z 1) * ((d 1 : ℝ) - 2) + r.p₁ - r.l₁ * z 1 = 0 := by
    linarith [hz1]
  have hdiff : (x 1 - z 1) * (r.κ₁ * (x 1 + z 1) * ((d 1 : ℝ) - 2) - r.l₁) = 0 := by
    linear_combination hx1' - hz1'
  have hbr : r.κ₁ * (x 1 + z 1) * ((d 1 : ℝ) - 2) - r.l₁ ≠ 0 := by
    have hsum : 0 < x 1 + z 1 := by linarith [hxp 1, hzp 1]
    have hneg : (x 1 + z 1) * ((d 1 : ℝ) - 2) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hsum.le (by linarith [hd1])
    have hmul : r.κ₁ * ((x 1 + z 1) * ((d 1 : ℝ) - 2)) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos r.pos.2.1.le hneg
    have hlt : r.κ₁ * (x 1 + z 1) * ((d 1 : ℝ) - 2) - r.l₁ < 0 := by
      linarith [hmul, r.pos.2.2.2.2.2]
    exact ne_of_lt hlt
  have hx1z1 : x 1 = z 1 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hbr
  -- the first steady-state equations determine `x 0`
  have hx0' : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0
      = r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) + r.p₀ := by
    linarith [hx0]
  have hz0' : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0
      = r.κ₁ * (d 0 : ℝ) * (z 1 * z 1) + r.p₀ := by
    linarith [hz0]
  have hp0 : 0 < r.p₀ := r.pos.2.2.1
  have hpos : 0 < r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) + r.p₀ := by
    have h1 : 0 ≤ r.κ₁ * (d 0 : ℝ) * (x 1 * x 1) := by
      exact mul_nonneg (mul_nonneg r.pos.2.1.le (Nat.cast_nonneg _)) (mul_self_nonneg _)
    linarith
  have hcoeff : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) := by
    have h2 : 0 < (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0 := by linarith [hx0', hpos]
    by_cases hc : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)
    · exact hc
    · have : r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) ≤ 0 := le_of_not_gt hc
      have : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg this (hxp 0).le
      linarith
  have hx0z0 : x 0 = z 0 := by
    have h3 : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0
        = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0 := by
      have hx0'' : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0
          = r.κ₁ * (d 0 : ℝ) * (z 1 * z 1) + r.p₀ := by
        have := hx0'
        simp only [hx1z1] at this
        exact this
      rw [hx0'', hz0']
    exact mul_left_cancel₀ hcoeff.ne' h3
  have hxyz : x = z := by
    funext s
    fin_cases s
    · exact hx0z0
    · exact hx1z1
  exact hne hxyz

/-- **Necessary condition for the sub-family `c = X + Y`: the second reaction must change the
number of `X` molecules.**  If `v₀ = (d 0 : ℝ) - (c 0 : ℝ) = 0`, then the first steady-state
equation determines `x₀` and the second determines `x₁`, so the positive steady state is unique
and the network is not multistationary.  The criterion `Network.twoRxnMultistationary` requires
`v₀ ≠ 0` in this sub-family. -/
theorem not_multistationary_of_c_XplusY_of_v0_zero
    (b d : Complex Sp2) (hd : d ∈ bimolecular) (hv0 : (d 0 : ℝ) - 1 = 0)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cXY d r x) (hz : TwoRxnSteady b cXY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) : False := by
  have hmonoX : (x 0) ^ (cXY 0) * (x 1) ^ (cXY 1) = x 0 * x 1 := by
    simp [cXY]
  have hmonoZ : (z 0) ^ (cXY 0) * (z 1) ^ (cXY 1) = z 0 * z 1 := by
    simp [cXY]
  have hx0 := hx.1
  have hx1 := hx.2
  have hz0 := hz.1
  have hz1 := hz.2
  rw [hmonoX] at hx0 hx1
  rw [hmonoZ] at hz0 hz1
  have hX0 : (cXY 0 : ℝ) = 1 := by norm_num [cXY]
  have hX1 : (cXY 1 : ℝ) = 1 := by norm_num [cXY]
  simp only [hX0, hX1] at hx0 hx1 hz0 hz1
  rw [hv0] at hx0 hz0
  -- `d` is bimolecular and `d 0 = 1`, so `d = X` or `d = X + Y`
  have hd0 : (d 0 : ℝ) = 1 := by linarith [hv0]
  have hdcases : d = cX ∨ d = cXY := by
    have hd' : d = Complex.zero ∨ d = cX ∨ d = cTwoX ∨ d = cY ∨ d = cTwoY ∨ d = cXY := by
      simpa [bimolecular] using hd
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Complex.zero] at hd0
    · exact Or.inl rfl
    · simp [cTwoX] at hd0
    · simp [cY] at hd0
    · simp [cTwoY] at hd0
    · exact Or.inr rfl
  have hd1 : (d 1 : ℝ) ≤ 1 := by
    rcases hdcases with rfl | rfl <;> norm_num [cX, cXY]
  -- the first steady-state equation determines `x 0`
  have hx0' : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0 = r.p₀ := by
    linarith [hx0]
  have hz0' : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0 = r.p₀ := by
    linarith [hz0]
  have hp0 : 0 < r.p₀ := r.pos.2.2.1
  have hcoeff : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) := by
    have h2 : 0 < (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0 := by linarith [hz0', hp0]
    by_cases hc : 0 < r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)
    · exact hc
    · have : r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1) ≤ 0 := le_of_not_gt hc
      have : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg this (hzp 0).le
      linarith
  have hx0z0 : x 0 = z 0 := by
    have h2 : (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * x 0
        = (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) * z 0 := by linarith [hx0', hz0']
    exact mul_left_cancel₀ hcoeff.ne' h2
  -- the second steady-state equation determines `x 1`
  have hx1' : (r.l₁ - r.κ₁ * x 0 * ((d 1 : ℝ) - 1)) * x 1
      = r.κ₀ * x 0 * (b 1 : ℝ) + r.p₁ := by
    linarith [hx1]
  have hz1' : (r.l₁ - r.κ₁ * z 0 * ((d 1 : ℝ) - 1)) * z 1
      = r.κ₀ * z 0 * (b 1 : ℝ) + r.p₁ := by
    linarith [hz1]
  have hp1 : 0 < r.p₁ := r.pos.2.2.2.1
  have hcoeff1 : 0 < r.l₁ - r.κ₁ * x 0 * ((d 1 : ℝ) - 1) := by
    have h1 : r.κ₁ * x 0 * ((d 1 : ℝ) - 1) ≤ 0 := by
      have h2 : 0 ≤ r.κ₁ * x 0 := mul_nonneg r.pos.2.1.le (hxp 0).le
      exact mul_nonpos_of_nonneg_of_nonpos h2 (by linarith [hd1])
    linarith [h1, r.pos.2.2.2.2.2]
  have hx1z1 : x 1 = z 1 := by
    have h4 : (r.l₁ - r.κ₁ * x 0 * ((d 1 : ℝ) - 1)) * x 1
        = (r.l₁ - r.κ₁ * x 0 * ((d 1 : ℝ) - 1)) * z 1 := by
      have hx1'' : (r.l₁ - r.κ₁ * x 0 * ((d 1 : ℝ) - 1)) * x 1
          = r.κ₀ * x 0 * (b 1 : ℝ) + r.p₁ := hx1'
      have hz1'' : (r.l₁ - r.κ₁ * x 0 * ((d 1 : ℝ) - 1)) * z 1
          = r.κ₀ * x 0 * (b 1 : ℝ) + r.p₁ := by
        have hz0x0 : z 0 = x 0 := hx0z0.symm
        have := hz1'
        simp only [hz0x0] at this
        exact this
      rw [hx1'', hz1'']
    exact mul_left_cancel₀ hcoeff1.ne' h4
  have hxyz : x = z := by
    funext s
    fin_cases s
    · exact hx0z0
    · exact hx1z1
  exact hne hxyz

/-- **Necessary condition for the sub-family `c = X + Y`: `Q' > 0`.**  With
`Q' = v₁ l₀ - κ₀ (v₁ u₀ - v₀ u₁)`, the elimination identity `v₀ l₁ x₁ = x₀ Q' + P'` applied to
the two steady states forces `Q' > 0`, whence `σ < 0`. -/
theorem twoRxn_multistationary_cXY_imp_Q_pos
    (b d : Complex Sp2) (hd : d ∈ bimolecular)
    (r : TwoRxnRates) (x z : Concentration Sp2)
    (hx : TwoRxnSteady b cXY d r x) (hz : TwoRxnSteady b cXY d r z)
    (hxp : x.Positive) (hzp : z.Positive) (hne : x ≠ z) :
    0 < ((d 1 : ℝ) - 1) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ)) := by
  have hmonoX : (x 0) ^ (cXY 0) * (x 1) ^ (cXY 1) = x 0 * x 1 := by
    simp [cXY]
  have hmonoZ : (z 0) ^ (cXY 0) * (z 1) ^ (cXY 1) = z 0 * z 1 := by
    simp [cXY]
  have hX0 : (cXY 0 : ℝ) = 1 := by norm_num [cXY]
  have hX1 : (cXY 1 : ℝ) = 1 := by norm_num [cXY]
  have hx0 := hx.1
  have hz0 := hz.1
  rw [hmonoX] at hx0
  rw [hmonoZ] at hz0
  simp only [hX0] at hx0 hz0
  -- `v₀ = d₀ - 1` is nonzero
  have hv0ne : (d 0 : ℝ) - 1 ≠ 0 := by
    intro h
    exact not_multistationary_of_c_XplusY_of_v0_zero b d hd h r x z hx hz hxp hzp hne
  -- the first coordinates of the two steady states differ
  have hx0z0 : x 0 ≠ z 0 := by
    intro h
    have hz0' : r.κ₀ * x 0 * ((b 0 : ℝ) - 1) + r.κ₁ * (x 0 * z 1) * ((d 0 : ℝ) - 1)
        + r.p₀ - r.l₀ * x 0 = 0 := by
      rw [← h] at hz0
      exact hz0
    have hsub : r.κ₁ * ((d 0 : ℝ) - 1) * (x 0 * x 1 - x 0 * z 1) = 0 := by
      linear_combination hx0 - hz0'
    have hmul : r.κ₁ * ((d 0 : ℝ) - 1) ≠ 0 := mul_ne_zero r.pos.2.1.ne' hv0ne
    have hprod : x 0 * x 1 = x 0 * z 1 := by
      rcases mul_eq_zero.mp hsub with hh | hh
      · exact absurd hh hmul
      · exact sub_eq_zero.mp hh
    have hx1z1 : x 1 = z 1 := by
      exact mul_left_cancel₀ (ne_of_gt (hxp 0)) hprod
    have hxyz : x = z := by
      funext s
      fin_cases s
      · exact h
      · exact hx1z1
    exact hne hxyz
  -- the elimination identity
  have helimX := twoRxnSteady_elim b cXY d r x hx
  have helimZ := twoRxnSteady_elim b cXY d r z hz
  simp only [hX0, hX1] at helimX helimZ
  -- the two first coordinates are the two roots of a quadratic
  have hquadX : r.κ₁
        * (((d 1 : ℝ) - 1) * r.l₀
          - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ))) * (x 0) ^ 2
      + (r.κ₁ * (((d 0 : ℝ) - 1) * r.p₁ - ((d 1 : ℝ) - 1) * r.p₀)
          - r.l₁ * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))) * x 0
      + r.l₁ * r.p₀ = 0 := by
    linear_combination r.l₁ * hx0 - r.κ₁ * x 0 * helimX
  have hquadZ : r.κ₁
        * (((d 1 : ℝ) - 1) * r.l₀
          - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ))) * (z 0) ^ 2
      + (r.κ₁ * (((d 0 : ℝ) - 1) * r.p₁ - ((d 1 : ℝ) - 1) * r.p₀)
          - r.l₁ * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))) * z 0
      + r.l₁ * r.p₀ = 0 := by
    linear_combination r.l₁ * hz0 - r.κ₁ * z 0 * helimZ
  -- Vieta: the product of the two roots is `l₁ p₀ / (κ₁ Q')`
  have hprod0 : (x 0 - z 0) * (r.κ₁
        * (((d 1 : ℝ) - 1) * r.l₀
          - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ))) * (x 0 + z 0)
      + r.κ₁ * (((d 0 : ℝ) - 1) * r.p₁ - ((d 1 : ℝ) - 1) * r.p₀)
      - r.l₁ * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1))) = 0 := by
    linear_combination hquadX - hquadZ
  have hlin : r.κ₁
        * (((d 1 : ℝ) - 1) * r.l₀
          - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ))) * (x 0 + z 0)
      + r.κ₁ * (((d 0 : ℝ) - 1) * r.p₁ - ((d 1 : ℝ) - 1) * r.p₀)
      - r.l₁ * (r.l₀ - r.κ₀ * ((b 0 : ℝ) - 1)) = 0 := by
    rcases mul_eq_zero.mp hprod0 with hh | hh
    · exact absurd hh (sub_ne_zero.mpr hx0z0)
    · exact hh
  have hprod : -r.κ₁
        * (((d 1 : ℝ) - 1) * r.l₀
          - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ))) * x 0 * z 0
      + r.l₁ * r.p₀ = 0 := by
    linear_combination hquadX - x 0 * hlin
  have hvieta : r.κ₁
        * (((d 1 : ℝ) - 1) * r.l₀
          - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ))) * x 0 * z 0
      = r.l₁ * r.p₀ := by linarith [hprod]
  have hpos : 0 < r.κ₁ * x 0 * z 0 := by
    have h1 : 0 < r.κ₁ * x 0 := mul_pos r.pos.2.1 (hxp 0)
    exact mul_pos h1 (hzp 0)
  have h1 : (((d 1 : ℝ) - 1) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ)))
      * (r.κ₁ * x 0 * z 0) = r.l₁ * r.p₀ := by
    calc (((d 1 : ℝ) - 1) * r.l₀
        - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ)))
        * (r.κ₁ * x 0 * z 0)
        = r.κ₁
          * (((d 1 : ℝ) - 1) * r.l₀
            - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ))) * x 0 * z 0 := by
          ring
    _ = r.l₁ * r.p₀ := hvieta
  have h2 : 0 < (((d 1 : ℝ) - 1) * r.l₀
      - r.κ₀ * (((d 1 : ℝ) - 1) * ((b 0 : ℝ) - 1) - ((d 0 : ℝ) - 1) * (b 1 : ℝ)))
      * (r.κ₁ * x 0 * z 0) := by
    have h3 : 0 < r.l₁ * r.p₀ := mul_pos r.pos.2.2.2.2.2 r.pos.2.2.1
    rw [h1]
    exact h3
  exact pos_of_mul_pos_left h2 hpos.le

#print axioms not_multistationary_of_c_twoY_of_b1_zero
#print axioms not_multistationary_of_c_XplusY_of_v0_zero
#print axioms twoRxn_multistationary_cXY_imp_Q_pos

end Network

end CRNT
