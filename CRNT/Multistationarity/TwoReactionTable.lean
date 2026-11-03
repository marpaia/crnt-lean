import CRNT.Multistationarity.TwoReactionCompleteness2

/-!
# The finite completeness of the two-reaction criterion table

This module closes the **finite** half of the two-reaction classification of multistationarity:
the kernel-decided table of the **75** two-species bimolecular two-reaction fully open networks
of `CRNT.Multistationarity.TwoReactionClassification` is now a **proved enumeration** and not
merely a list of verified examples.

## The setting

There are two species, `X` (index `0`) and `Y` (index `1`); the two non-flow reactions of the
canonical network are `X → b` and `c → d`, where `b`, `c`, `d` are **bimolecular** complexes
(at most two molecules each).  The family is the list

```
twoReactionFamily : List (Complex Sp2 × Complex Sp2 × Complex Sp2)
```

of the **75** triples `(b, c, d)` with `b ∈ {0, 2X, Y, 2Y, X+Y}`, `c ∈ {2X, X+Y, 2Y}` and
`d ∈ {0, X, 2X, Y, 2Y, X+Y} \ {c}` (`twoReactionFamily_card`).

This is the two-species, *directed* sub-family of the enumeration of Joshi and Shiu, *Atoms of
multistationarity in chemical reaction networks* (J. Math. Chem. **51** (2013), 153–178), §6,
who enumerate the *reversible* bimolecular two-reaction networks up to relabelling of the species
and find 386 of them, 35 of which are multistationary, with 11 minimal elements — the bimolecular
two-reaction atoms of multistationarity.  See also their *A sharp bound on the number of
equilibria of a two-reaction network*, the two-reaction case of the general bound.

## What the repository already has

* the **closed-form** `Bool` criterion `twoRxnMultistationary`, which reads, with `u = b - X` and
  `v = d - c` the two reaction vectors and `σ = v₁ u₀ - v₀ u₁`:

  * `c = 2X`: the network is **never** multistationary;
  * `c = X + Y`: the network is multistationary iff `v₀ ≠ 0` and either
    (`v₀ > 0` and `σ < 0` and `u₁ > 0`) or (`v₀ < 0`, `v₁ < 0` and `σ < 0`);
  * `c = 2Y`: the network is multistationary iff `v₀ > 0`, `σ < 0` and `u₁ > 0`;

* the **kernel-decided tables** `twoReaction_criterion_table` and `twoReaction_atom_table` of
  `CRNT.Multistationarity.TwoReactionClassification`, together with the soundness of the
  criterion (`twoRxnMultistationary_sound`) and the explicit witnesses `witness_1` … `witness_8`
  for the eight multistationary members (`multistationaryList_mem`, `multistationaryList_atom`);

* the **analytic completeness** of the criterion, proved by the campaign in
  `CRNT.Multistationarity.TwoReactionCompleteness` and
  `CRNT.Multistationarity.TwoReactionCompleteness2`: the necessary conditions
  `not_multistationary_of_c_twoY_of_b1_zero`, `not_multistationary_of_c_XplusY_of_v0_zero`,
  `twoRxn_multistationary_cXY_imp_Q_pos`, `twoRxn_multistationary_cXY_imp_sigma_neg`,
  `twoRxn_multistationary_cXY_imp_u1_pos`, `twoRxn_multistationary_cXY_imp_v1_neg`,
  `twoRxn_multistationary_cTwoY_imp_v0_pos`, `twoRxn_multistationary_cTwoY_imp_Q_pos`,
  `twoRxn_multistationary_cTwoY_imp_sigma_neg`, and with them the payoff
  `twoRxnMultistationary_complete_cXY` and `twoRxnMultistationary_complete_cTwoY`.

## What this module adds: the *finite* completeness of the table

The tables of the classification module are *finite* statements, discharged by the kernel `decide`;
what was still missing is the statement that they are **complete enumerations**, i.e. that they
decide the property on **every one** of the 75 members and not only on the members they list.

* `twoRxnMultistationary_complete` — the completeness of the criterion on the **whole** family:
  the three possible sources `c = 2X`, `c = X + Y`, `c = 2Y` are treated in a single statement.
  This is the finite complement of the analytic completeness of the campaign's two modules.

* `twoReaction_criterion_iff_multistationary` — the criterion **decides** multistationarity on
  every one of the 75 members: `twoRxnMultistationary b c d = true` iff the network
  `twoRxnOpen cX b c d` has the capacity for multiple positive steady states.

* `twoReaction_criterionTable_eq_criterion` — the **finite agreement** of the table with the
  criterion on every member: the verdict of the table (membership in `multistationaryList`) and
  the value of the closed-form criterion coincide on all 75 members.

* `twoReaction_criterionTable_complete` — the table is a **complete enumeration** of
  multistationarity: on every one of the 75 members the verdict of the table coincides with the
  actual multistationarity property of the network.

* `twoReaction_multistationaryMembers_eq` — the multistationary members of the family are
  **exactly** the ones the table lists.

* `twoReaction_atomTable_eq_atom` — the **atom** table is complete: a member of the family is an
  atom of multistationarity (`TwoRxnIsAtom cX b c d`) if and only if the atom table lists it.

* `twoReaction_table_witness`, `twoReaction_witness_iff_criterion` — each member of the table has
  an **explicit witness** (six strictly positive rate constants and two distinct positive
  concentrations that are both steady states), and the existence of such a witness characterises
  the members of the table among the 75.

* `twoReaction_atom_no_multistationary_subnetwork` — each atom member of the table is **not** a
  proper enlargement of a multistationary subnetwork: its two one-reaction subnetwork extensions
  are monostationary.

* `twoReaction_criterionTable`, `twoReaction_atomTable` — the two tables *as lists*, of the
  members of the family selected by the criterion resp. by the atom table, read in the order in
  which the family lists them; `twoReaction_criterionTable_perm` and `twoReaction_atomTable_perm`
  record that they are permutations of `multistationaryList` resp. `atomList`.

## The orientation of the table

`twoReactionFamily` lists the triples `(b, c, d)` in the order (target of the first reaction,
source of the second reaction, target of the second reaction), and `twoReaction_criterion_table`
reads the triple as `N.1`, `N.2.1`, `N.2.2` — in the **same** order.  No reordering of the
triple is therefore needed.

What *does* differ is the order of the elements of `multistationaryList`: for a fixed `b` it lists
the members with source `c = 2Y` *before* those with source `c = X + Y`, whereas the family lists
`c = X + Y` first.  Consequently the statement

```
twoReactionFamily.filter (fun N => twoRxnMultistationary N.1 N.2.1 N.2.2) = multistationaryList
```

is **false**; the correct statement is that the two lists are **permutations** of each other
(`twoReaction_criterionTable_perm`), or, equivalently, that they have the same members
(`twoReaction_multistationaryMembers_eq`).

## What is *not* claimed

* The criterion is **not** claimed outside the two-species bimolecular family: not for reversible
  two-reaction networks, not for more than two species, not for complexes that are not
  bimolecular, and not as a criterion for the *number* of positive steady states.
* The **atom enumeration** of Joshi–Shiu for the full (reversible, any number of species)
  bimolecular two-reaction family, with its 386 networks and 11 atoms, is **not** reproduced here;
  the family of this module is the 75-member two-species sub-family of it, with its eight
  multistationary members and its eight atoms.
* These are the items that remain open in leaf **M11** of `docs/field-map.md`.

## Literature

* A. Joshi and W. Shiu, *Atoms of multistationarity in chemical reaction networks*,
  J. Math. Chem. **51** (2013), 153–178 — §6 enumerates the reversible bimolecular two-reaction
  networks; 35 of the 386 admit multiple positive mass-action steady states and the corresponding
  poset has 11 minimal elements.
* A. Joshi and W. Shiu, *A sharp bound on the number of equilibria of a two-reaction network* —
  the two-reaction case of the general bound.
-/

namespace CRNT

namespace Network

open scoped BigOperators

/-! ### The verdicts of the two tables -/

/-- **The verdict of the classification table** on a member of the family: `true` if and only if
the member is listed in `multistationaryList`. -/
def twoReaction_tableVerdict (N : Complex Sp2 × Complex Sp2 × Complex Sp2) : Bool :=
  decide (N ∈ multistationaryList)

/-- **The verdict of the atom table** on a member of the family: `true` if and only if the member
is listed in `atomList`. -/
def twoReaction_atomVerdict (N : Complex Sp2 × Complex Sp2 × Complex Sp2) : Bool :=
  decide (N ∈ atomList)

/-- **The two tables have the same verdict** on every member: `atomList` and `multistationaryList`
are the same list, because a bimolecular one-reaction network is never multistationary, so a
multistationary two-reaction network of the family is automatically an atom. -/
theorem twoReaction_atomVerdict_eq_tableVerdict (N : Complex Sp2 × Complex Sp2 × Complex Sp2) :
    twoReaction_atomVerdict N = twoReaction_tableVerdict N := by
  rfl

/-! ### The shape of the family -/

/-- **The three complexes of a member of the family are bimolecular.** -/
theorem twoReactionFamily_bimolecular :
    ∀ N ∈ twoReactionFamily,
      N.1 ∈ bimolecular ∧ N.2.1 ∈ bimolecular ∧ N.2.2 ∈ bimolecular := by
  decide

/-- **The source of the second reaction of a member of the family is `2X`, `X + Y` or `2Y`.** -/
theorem twoReactionFamily_source :
    ∀ N ∈ twoReactionFamily, N.2.1 = cTwoX ∨ N.2.1 = cXY ∨ N.2.1 = cTwoY := by
  decide

/-- **The eight multistationary members are members of the family.** -/
theorem multistationaryList_subset_family : ∀ N ∈ multistationaryList, N ∈ twoReactionFamily := by
  decide

/-- **The eight atom members are members of the family.** -/
theorem atomList_subset_family : ∀ N ∈ atomList, N ∈ twoReactionFamily := by
  decide

/-! ### The completeness of the criterion on the whole family -/

/-- **The criterion is complete on the whole family.**  If a member of the seventy-five-member
family is multistationary, then the closed-form criterion `twoRxnMultistationary` holds.  The
three possible sources of the second reaction are treated in one statement: the source `c = 2X` is
discharged by `not_multistationary_of_c_twoX` (and the criterion is `false` there by definition),
the sources `c = X + Y` and `c = 2Y` by `twoRxnMultistationary_complete_cXY` resp.
`twoRxnMultistationary_complete_cTwoY`.  Together with the soundness
`twoRxnMultistationary_sound` this makes `twoRxnMultistationary` an **exact decision procedure**
for multistationarity on the family. -/
theorem twoRxnMultistationary_complete (b c d : Complex Sp2) (hN : (b, c, d) ∈ twoReactionFamily)
    (h : (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity) :
    twoRxnMultistationary b c d = true := by
  have hcd : c = cTwoX ∨ c = cXY ∨ c = cTwoY := twoReactionFamily_source (b, c, d) hN
  have hd : d ∈ bimolecular := (twoReactionFamily_bimolecular (b, c, d) hN).2.2
  rcases hcd with rfl | rfl | rfl
  · exact absurd h (not_multistationary_of_c_twoX b cTwoX d rfl hd)
  · exact twoRxnMultistationary_complete_cXY b d hd h
  · exact twoRxnMultistationary_complete_cTwoY b d hd h

/-- **The criterion decides multistationarity on every member of the family.** -/
theorem twoReaction_criterion_iff_multistationary :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ twoReactionFamily →
      ((twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity ↔
        twoRxnMultistationary b c d = true) := by
  intro b c d hN
  constructor
  · exact twoRxnMultistationary_complete b c d hN
  · intro h
    exact (twoRxnMultistationary_sound b c d hN h).1

/-! ### The finite completeness of the two tables -/

/-- **The criterion table is complete.**  For every member of the seventy-five-member two-species
bimolecular two-reaction family, the kernel-decided table `twoReaction_criterion_table` agrees
with the closed-form criterion `twoRxnMultistationary`: the verdict of the table (membership in
`multistationaryList`) and the value of the criterion coincide.  This upgrades the table from a
list of verified examples to a *complete* enumeration. -/
theorem twoReaction_criterionTable_eq_criterion :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ twoReactionFamily →
      twoReaction_tableVerdict (b, c, d) = twoRxnMultistationary b c d := by
  intro b c d hN
  have htab := twoReaction_criterion_table (b, c, d) hN
  by_cases hmem : (b, c, d) ∈ multistationaryList
  · have hcrit : twoRxnMultistationary b c d = true := htab.mpr hmem
    simp [twoReaction_tableVerdict, hmem, hcrit]
  · have hcrit : twoRxnMultistationary b c d = false := by
      cases hc : twoRxnMultistationary b c d with
      | false => rfl
      | true => exact absurd (htab.mp hc) hmem
    simp [twoReaction_tableVerdict, hmem, hcrit]

/-- **The atom table agrees with the criterion on every member of the family.** -/
theorem twoReaction_atomTable_eq_criterion :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ twoReactionFamily →
      twoReaction_atomVerdict (b, c, d) = twoRxnMultistationary b c d := by
  intro b c d hN
  rw [twoReaction_atomVerdict_eq_tableVerdict]
  exact twoReaction_criterionTable_eq_criterion b c d hN

/-- **The multistationary members of the family are exactly the ones the table lists.**  This is
the *finite completeness* of the enumeration: the eight members of `multistationaryList` are all
the multistationary members of the family, and there is no further one. -/
theorem twoReaction_multistationaryMembers_eq :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ twoReactionFamily →
      ((twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity ↔
        (b, c, d) ∈ multistationaryList) := by
  intro b c d hN
  constructor
  · intro h
    have hcrit : twoRxnMultistationary b c d = true := twoRxnMultistationary_complete b c d hN h
    exact (twoReaction_criterion_table (b, c, d) hN).mp hcrit
  · intro h
    have hcrit : twoRxnMultistationary b c d = true :=
      (twoReaction_criterion_table (b, c, d) hN).mpr h
    exact (twoRxnMultistationary_sound b c d hN hcrit).1

/-- **The criterion table is a complete enumeration of multistationarity.**  On every one of the
seventy-five members of the family the verdict of the table coincides with the actual
multistationarity property of the network: the table is not merely a list of verified examples,
it decides the property on the whole family. -/
theorem twoReaction_criterionTable_complete :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ twoReactionFamily →
      ((twoReaction_tableVerdict (b, c, d) = true) ↔
        (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity) := by
  intro b c d hN
  constructor
  · intro h
    have hcrit : twoRxnMultistationary b c d = true := by
      rw [← twoReaction_criterionTable_eq_criterion b c d hN]
      exact h
    exact (twoRxnMultistationary_sound b c d hN hcrit).1
  · intro h
    have hcrit : twoRxnMultistationary b c d = true := twoRxnMultistationary_complete b c d hN h
    rw [twoReaction_criterionTable_eq_criterion b c d hN]
    exact hcrit

/-- **The atom table is complete.**  For every member of the family, the table `atomList` agrees
with the atom property of the network: the fully open network `twoRxnOpen cX b c d` is an atom of
multistationarity if and only if the atom table lists the member. -/
theorem twoReaction_atomTable_eq_atom :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ twoReactionFamily →
      (TwoRxnIsAtom cX b c d ↔ (b, c, d) ∈ atomList) := by
  intro b c d hN
  constructor
  · intro h
    have hmulti : (twoRxnOpen cX b c d).fullyOpen.HasMultistationarityCapacity := h.1
    have hcrit : twoRxnMultistationary b c d = true := twoRxnMultistationary_complete b c d hN hmulti
    have hmem : (b, c, d) ∈ multistationaryList :=
      (twoReaction_criterion_table (b, c, d) hN).mp hcrit
    simpa [atomList] using hmem
  · intro h
    have hcrit : twoRxnMultistationary b c d = true :=
      (twoReaction_criterion_table (b, c, d) hN).mpr (by simpa [atomList] using h)
    exact (twoRxnMultistationary_sound b c d hN hcrit).2

/-! ### The tables as lists -/

/-- **The criterion table, as a list**: the members of the family selected by the closed-form
criterion, read in the order in which the family lists them. -/
def twoReaction_criterionTable : List (Complex Sp2 × Complex Sp2 × Complex Sp2) :=
  twoReactionFamily.filter (fun N => twoRxnMultistationary N.1 N.2.1 N.2.2)

/-- **The atom table, as a list**: the members of the family selected by the atom table, read in
the order in which the family lists them. -/
def twoReaction_atomTable : List (Complex Sp2 × Complex Sp2 × Complex Sp2) :=
  twoReactionFamily.filter (fun N => twoReaction_atomVerdict N)

/-- **The criterion table has eight members.** -/
theorem twoReaction_criterionTable_length : twoReaction_criterionTable.length = 8 := by decide

/-- **The atom table has eight members.** -/
theorem twoReaction_atomTable_length : twoReaction_atomTable.length = 8 := by decide

/-- **The criterion table is a permutation of `multistationaryList`.**  The two lists have the
same members; they differ only in the order, the family listing the members with source
`c = X + Y` before those with source `c = 2Y`. -/
theorem twoReaction_criterionTable_perm :
    List.Perm twoReaction_criterionTable multistationaryList := by decide

/-- **The atom table is a permutation of `atomList`.** -/
theorem twoReaction_atomTable_perm :
    List.Perm twoReaction_atomTable atomList := by decide

/-- **Every member of the criterion table is listed in `multistationaryList`.** -/
theorem twoReaction_criterionTable_mem :
    ∀ N ∈ twoReaction_criterionTable, N ∈ multistationaryList := by
  intro N hN
  have hN' := List.mem_filter.mp hN
  exact (twoReaction_criterion_table N hN'.1).mp hN'.2

/-- **Every member of `multistationaryList` is in the criterion table.** -/
theorem twoReaction_criterionTable_covers :
    ∀ N ∈ multistationaryList, N ∈ twoReaction_criterionTable := by
  intro N hN
  have hN' : N ∈ twoReactionFamily := multistationaryList_subset_family N hN
  refine List.mem_filter.mpr ⟨hN', ?_⟩
  exact (twoReaction_criterion_table N hN').mpr hN

/-! ### The witnesses -/

/-- **Every multistationary member of the table has an explicit witness**: six strictly positive
rate constants and two distinct positive concentrations which are both steady states of the fully
open network. -/
theorem twoReaction_table_witness (b c d : Complex Sp2) (hN : (b, c, d) ∈ multistationaryList) :
    ∃ (r : TwoRxnRates) (x z : Concentration Sp2),
      x.Positive ∧ z.Positive ∧ x ≠ z ∧ TwoRxnSteady b c d r x ∧ TwoRxnSteady b c d r z := by
  obtain ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩ :=
    (twoRxnOpen_multistationary_iff b c d).mp (multistationaryList_mem b c d hN)
  exact ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩

/-- **The witness characterisation.**  A member of the family admits two distinct positive steady
states for a suitable choice of rate constants if and only if the criterion holds; the eight
members of the table are thus exactly the members of the family that admit such a witness. -/
theorem twoReaction_witness_iff_criterion :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ twoReactionFamily →
      ((∃ (r : TwoRxnRates) (x z : Concentration Sp2),
          x.Positive ∧ z.Positive ∧ x ≠ z ∧ TwoRxnSteady b c d r x ∧ TwoRxnSteady b c d r z)
        ↔ twoRxnMultistationary b c d = true) := by
  intro b c d hN
  constructor
  · rintro ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩
    exact twoRxnMultistationary_complete b c d hN
      ((twoRxnOpen_multistationary_iff b c d).mpr ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩)
  · intro h
    obtain ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩ :=
      (twoRxnOpen_multistationary_iff b c d).mp (twoRxnMultistationary_sound b c d hN h).1
    exact ⟨r, x, z, hxp, hzp, hne, hxs, hzs⟩

/-- **Each atom member of the table is not a proper enlargement of a multistationary
subnetwork**: its two one-reaction subnetwork extensions are monostationary. -/
theorem twoReaction_atom_no_multistationary_subnetwork :
    ∀ (b c d : Complex Sp2), (b, c, d) ∈ atomList →
      ¬ (oneRxn cX b).fullyOpen.HasMultistationarityCapacity ∧
      ¬ (oneRxn c d).fullyOpen.HasMultistationarityCapacity := by
  intro b c d hN
  have h := (multistationaryList_atom b c d (by simpa [atomList] using hN)).1
  exact ⟨h.2.1, h.2.2⟩

/-- **A non-vacuity check for the table.**  The member `X → 2X`, `X + Y → 0` of the family — the
first member of `multistationaryList`, with the explicit witness `witness_1` — is selected by the
criterion, is multistationary and is an atom of multistationarity. -/
theorem twoReaction_table_witness_check :
    twoRxnMultistationary cTwoX cXY Complex.zero = true ∧
      (twoRxnOpen cX cTwoX cXY Complex.zero).fullyOpen.HasMultistationarityCapacity ∧
      TwoRxnIsAtom cX cTwoX cXY Complex.zero := by
  refine ⟨?_, ?_, ?_⟩
  · exact (twoReaction_criterion_table (cTwoX, cXY, Complex.zero) (by decide)).mpr (by
      simp [multistationaryList])
  · exact multistationaryList_mem cTwoX cXY Complex.zero (by simp [multistationaryList])
  · exact (multistationaryList_atom cTwoX cXY Complex.zero (by simp [multistationaryList])).1

#print axioms twoReaction_criterionTable_eq_criterion
#print axioms twoReaction_criterionTable_complete
#print axioms twoReaction_atomTable_eq_criterion
#print axioms twoReaction_atomTable_eq_atom
#print axioms twoReaction_multistationaryMembers_eq
#print axioms twoReaction_criterion_iff_multistationary
#print axioms twoRxnMultistationary_complete
#print axioms twoReaction_criterionTable_perm
#print axioms twoReaction_atomTable_perm
#print axioms twoReaction_table_witness
#print axioms twoReaction_witness_iff_criterion
#print axioms twoReaction_atom_no_multistationary_subnetwork

end Network

end CRNT
