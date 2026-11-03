import CRNT.Multistationarity.SRGraph
import CRNT.Graph.Reversibility
import Mathlib.Data.Quot

/-!
# The true-chemistry Species--Reaction graph

The classical Shinar--Feinberg / Craciun--Feinberg SR graph is slightly more
structured than the incidence graph in `SRGraph.lean`:

* a reversible pair is represented by a single reaction vertex;
* flow/degradation channels can be omitted when considering the "true chemistry";
* every species--reaction edge remembers both its stoichiometric coefficient and
  the endpoint complex from which that coefficient came;
* c-pairs and s-cycles are defined from those endpoint labels.

This file keeps that object separate from the existing unsigned per-channel SR graph,
so the two notions cannot accidentally be conflated.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Two channels represent the same true chemical reaction when they have the same
unordered pair of endpoint complexes.  Thus opposite directions of a reversible pair
belong to one true-reaction class, as do parallel channels. -/
def SameTrueReaction (N : Network S) (r q : N.R) : Prop :=
  ((N.reaction r).source = (N.reaction q).source ∧
    (N.reaction r).target = (N.reaction q).target) ∨
  ((N.reaction r).source = (N.reaction q).target ∧
    (N.reaction r).target = (N.reaction q).source)

@[refl] theorem sameTrueReaction_refl (N : Network S) (r : N.R) :
    N.SameTrueReaction r r := Or.inl ⟨rfl, rfl⟩

@[symm] theorem sameTrueReaction_symm {N : Network S} {r q : N.R}
    (h : N.SameTrueReaction r q) : N.SameTrueReaction q r := by
  rcases h with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

@[trans] theorem sameTrueReaction_trans {N : Network S} {r q p : N.R}
    (hrq : N.SameTrueReaction r q) (hqp : N.SameTrueReaction q p) :
    N.SameTrueReaction r p := by
  -- Four orientation cases of equality of unordered endpoint pairs.
  rcases hrq with h | h <;> rcases hqp with k | k
  · exact Or.inl ⟨h.1.trans k.1, h.2.trans k.2⟩
  · exact Or.inr ⟨h.1.trans k.1, h.2.trans k.2⟩
  · exact Or.inr ⟨h.1.trans k.2, h.2.trans k.1⟩
  · exact Or.inl ⟨h.1.trans k.2, h.2.trans k.1⟩

/-- Setoid of true reaction vertices. -/
def trueReactionSetoid (N : Network S) : Setoid N.R where
  r := N.SameTrueReaction
  iseqv := ⟨N.sameTrueReaction_refl, @sameTrueReaction_symm _ _ _ N,
    @sameTrueReaction_trans _ _ _ N⟩

/-- A true-chemistry reaction vertex, identifying parallel and reverse channels. -/
abbrev TrueReaction (N : Network S) := Quotient N.trueReactionSetoid

/-- Quotient map from reaction channels to true reaction vertices. -/
def trueReaction (N : Network S) (r : N.R) : N.TrueReaction :=
  Quotient.mk N.trueReactionSetoid r

/-- Flow channels are omitted from the true chemistry.  This intentionally treats
any reaction incident to the zero complex as an externally imposed flow. -/
def IsFlowChannel (N : Network S) (r : N.R) : Prop :=
  (N.reaction r).source = Complex.zero ∨ (N.reaction r).target = Complex.zero

/-- A true reaction class is internal if it has an internal representative. -/
def TrueReaction.Internal (N : Network S) (ρ : N.TrueReaction) : Prop :=
  Quotient.liftOn ρ (fun r => ¬ N.IsFlowChannel r) (by
    intro r q h
    apply propext
    constructor
    · intro hnr hnq
      apply hnr
      rcases h with hsame | hswap
      · rcases hnq with hqs | hqt
        · exact Or.inl (hsame.1.trans hqs)
        · exact Or.inr (hsame.2.trans hqt)
      · rcases hnq with hqs | hqt
        · exact Or.inr (hswap.2.trans hqs)
        · exact Or.inl (hswap.1.trans hqt)
    · intro hnq hnr
      apply hnq
      rcases h with hsame | hswap
      · rcases hnr with hrs | hrt
        · exact Or.inl (hsame.1.symm.trans hrs)
        · exact Or.inr (hsame.2.symm.trans hrt)
      · rcases hnr with hrs | hrt
        · exact Or.inr (hswap.1.symm.trans hrs)
        · exact Or.inl (hswap.2.symm.trans hrt))

/-- Internal true-reaction vertices.  Keeping the internality proof in the vertex type makes
flow-channel omission structural rather than a convention carried only by comments. -/
abbrev InternalTrueReaction (N : Network S) := {ρ : N.TrueReaction // TrueReaction.Internal N ρ}

/-- True-chemistry SR vertices: species together with internal reaction classes only. -/
abbrev TrueSRVertex (N : Network S) := S ⊕ N.InternalTrueReaction

/-- A labeled species--reaction incidence edge.  The `endpoint` field is the source
or target complex that supplies this particular edge label. -/
structure TrueSREdge (N : Network S) where
  species : S
  reaction : N.TrueReaction
  /-- Only internal true-reaction classes occur as vertices of the true chemistry. -/
  internal : TrueReaction.Internal N reaction
  endpoint : Complex S
  representative : N.R
  representative_class : N.trueReaction representative = reaction
  endpoint_is_source_or_target :
    endpoint = (N.reaction representative).source ∨
      endpoint = (N.reaction representative).target
  occurs : endpoint species ≠ 0

/-- Stoichiometric label carried by an SR edge. -/
def TrueSREdge.coeff {N : Network S} (e : N.TrueSREdge) : ℕ :=
  e.endpoint e.species

/-- Every true SR edge has a positive stoichiometric label. -/
theorem TrueSREdge.coeff_pos {N : Network S} (e : N.TrueSREdge) : 0 < e.coeff :=
  Nat.pos_of_ne_zero e.occurs

/-- Two edges adjacent to the same reaction vertex form a c-pair when their complex
labels are the same endpoint complex. -/
def TrueSREdge.CPair {N : Network S} (e f : N.TrueSREdge) : Prop :=
  e.reaction = f.reaction ∧ e.endpoint = f.endpoint

/-- An alternating SR cycle is encoded as species `sᵢ`, reaction vertices `Rᵢ`, and
the two labeled edges `sᵢ--Rᵢ--sᵢ₊₁` at each reaction vertex.  Simplicity is recorded
explicitly; the encoding is finite and independent of graph-library walk choices. -/
structure TrueSRCycle (N : Network S) (n : ℕ) where
  nontrivial : 2 ≤ n
  species : Fin n → S
  reaction : Fin n → N.TrueReaction
  leftEdge : ∀ i : Fin n, N.TrueSREdge
  rightEdge : ∀ i : Fin n, N.TrueSREdge
  left_species : ∀ i, (leftEdge i).species = species i
  left_reaction : ∀ i, (leftEdge i).reaction = reaction i
  right_species : ∀ i,
    (rightEdge i).species = species ⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩
  right_reaction : ∀ i, (rightEdge i).reaction = reaction i
  species_injective : Function.Injective species
  reaction_injective : Function.Injective reaction

/-- A reaction vertex along the cycle contributes a c-pair when its two cycle edges
carry the same endpoint-complex label. -/
def TrueSRCycle.isCPair {N : Network S} {n : ℕ}
    (C : N.TrueSRCycle n) (i : Fin n) : Prop :=
  (C.leftEdge i).endpoint = (C.rightEdge i).endpoint

/-- Number of c-pairs along a finite true-SR cycle. -/
noncomputable def TrueSRCycle.numCPairs {N : Network S} {n : ℕ}
    (C : N.TrueSRCycle n) : ℕ := by
  classical
  exact (Finset.univ.filter C.isCPair).card

/-- Classical e-cycle: an even number of c-pairs. -/
def TrueSRCycle.Even {N : Network S} {n : ℕ} (C : N.TrueSRCycle n) : Prop :=
  _root_.Even C.numCPairs

/-- Stoichiometric s-cycle.  Alternately multiplying/dividing edge labels equals one;
we avoid division by cross-multiplying the alternating products. -/
def TrueSRCycle.SCycle {N : Network S} {n : ℕ} (C : N.TrueSRCycle n) : Prop :=
  (∏ i : Fin n, (C.leftEdge i).coeff) =
    ∏ i : Fin n, (C.rightEdge i).coeff

/-- **Net-coefficient s-cycle.**  The alternating product identity taken with the absolute net
coefficients `|target s - source s|` in place of the edge labels `TrueSREdge.coeff`.

Under `ReactantProductSeparated` this is the same condition as `SCycle`, since a species then
occurs on only one side of a reaction and the label of each edge *is* the absolute net
coefficient (`edge_coeff_eq_abs_reactionVector`).  Shinar--Feinberg assume separation
throughout, so both readings are faithful to the published s-cycle condition; they come apart
only for networks the published proof does not consider.

This variant is recorded because it is the quantity the kernel relation `InKerL α` actually
constrains: the strict cyclic gain derived from a strong-concordance witness compares
`|reactionVector|` products, not label products. -/
def TrueSREdge.netCoeff {N : Network S} (e : N.TrueSREdge) : ℝ :=
  |((N.reaction e.representative).target e.species : ℝ)
    - ((N.reaction e.representative).source e.species : ℝ)|

/-- The net-coefficient alternating product identity. -/
def TrueSRCycle.SCycleNet {N : Network S} {n : ℕ} (C : N.TrueSRCycle n) : Prop :=
  (∏ i : Fin n, (C.leftEdge i).netCoeff) = ∏ i : Fin n, (C.rightEdge i).netCoeff

/-- If every stoichiometric edge coefficient is one, every SR cycle is an s-cycle. -/
theorem TrueSRCycle.sCycle_of_all_coeff_one {N : Network S} {n : ℕ}
    (C : N.TrueSRCycle n)
    (hL : ∀ i, (C.leftEdge i).coeff = 1)
    (hR : ∀ i, (C.rightEdge i).coeff = 1) : C.SCycle := by
  simp [TrueSRCycle.SCycle, hL, hR]

/-- Two labeled true-SR edges represent the same graph edge when they have the
same species endpoint, true-reaction endpoint, and complex label.  The concrete
reaction representative and proof fields are implementation details and must not enter
graph-edge identity. -/
def TrueSREdge.SameIncidence {N : Network S} (e f : N.TrueSREdge) : Prop :=
  e.species = f.species ∧ e.reaction = f.reaction ∧ e.endpoint = f.endpoint

/-- Two true-SR edges share a graph vertex. -/
def TrueSREdge.ShareVertex {N : Network S} (e f : N.TrueSREdge) : Prop :=
  e.species = f.species ∨ e.reaction = f.reaction

/-- The two vertices are exactly the endpoints of the edge, in either order. -/
def TrueSREdge.Connects {N : Network S} (e : N.TrueSREdge)
    (u v : N.TrueSRVertex) : Prop :=
  (u = Sum.inl e.species ∧ v = Sum.inr ⟨e.reaction, e.internal⟩) ∨
    (u = Sum.inr ⟨e.reaction, e.internal⟩ ∧ v = Sum.inl e.species)

/-- An edge occurs on a true-SR cycle, modulo the proof-irrelevant choice of concrete
reaction representative. -/
def TrueSRCycle.ContainsEdge {N : Network S} {n : ℕ}
    (C : N.TrueSRCycle n) (e : N.TrueSREdge) : Prop :=
  (∃ i : Fin n, e.SameIncidence (C.leftEdge i)) ∨
    (∃ i : Fin n, e.SameIncidence (C.rightEdge i))

/-- Exact certificate that two cycles have a species-to-reaction intersection.

The classical definition says that the *entire* common-edge subgraph is nonempty and
that every one of its connected components is a simple path with a species vertex at
one end and a reaction vertex at the other.  We encode those components explicitly:
each component is a nonempty simple alternating edge/vertex path; `covers_common`
ensures that no common edge has been omitted; and `components_separated` ensures that
a connected common component has not been artificially split into several paths.

This is intentionally stronger than merely exhibiting one common S-to-R path.  The
latter is not the Shinar--Feinberg notion when the intersection has several connected
components. -/
structure TrueSRCycle.SToRIntersection {N : Network S} {m n : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n) where
  componentCount : ℕ
  componentCount_pos : 0 < componentCount
  componentLength : Fin componentCount → ℕ
  componentLength_pos : ∀ c, 0 < componentLength c
  edge : ∀ c, Fin (componentLength c) → N.TrueSREdge
  vertex : ∀ c, Fin (componentLength c + 1) → N.TrueSRVertex
  /-- Every listed edge is common to the two cycles. -/
  edge_on_C : ∀ c i, C.ContainsEdge (edge c i)
  edge_on_D : ∀ c i, D.ContainsEdge (edge c i)
  /-- Consecutive vertices are joined by the corresponding common edge. -/
  connects : ∀ c i,
    (edge c i).Connects (vertex c (Fin.castSucc i)) (vertex c i.succ)
  /-- Each connected component is represented by a simple edge path. -/
  edge_simple : ∀ c {i j},
    (edge c i).SameIncidence (edge c j) → i = j
  vertex_simple : ∀ c, Function.Injective (vertex c)
  /-- Every component begins at a species vertex.  Since paths are unoriented, this
  merely chooses one of the two possible path orientations. -/
  starts_at_species : ∀ c, ∃ s : S,
    vertex c 0 = Sum.inl s
  /-- Every component ends at a reaction vertex. -/
  ends_at_reaction : ∀ c, ∃ ρ : N.InternalTrueReaction,
    vertex c (Fin.last (componentLength c)) = Sum.inr ρ
  /-- The listed components cover the entire common-edge subgraph. -/
  covers_common : ∀ e : N.TrueSREdge,
    C.ContainsEdge e → D.ContainsEdge e →
      ∃ c, ∃ i, e.SameIncidence (edge c i)
  /-- Distinct listed components share no vertex, so a connected component cannot be
  split into several separately listed S-to-R paths. -/
  components_separated : ∀ {c d}, c ≠ d → ∀ i j,
    ¬ (edge c i).ShareVertex (edge d j)

/-- Orientation-free Shinar--Feinberg SR condition. -/
def TrueSRStrongCriterion (N : Network S) : Prop :=
  (∀ {n : ℕ} (C : N.TrueSRCycle n), C.Even → C.SCycle) ∧
  (∀ {m n : ℕ} (C : N.TrueSRCycle m) (D : N.TrueSRCycle n),
    C.Even → D.Even → ¬ Nonempty (C.SToRIntersection D))

end Network
end CRNT
