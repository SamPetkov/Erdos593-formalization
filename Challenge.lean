import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Order

/-!
# Erdős Problem 593: protected statement

This Mathlib-only module states the central finite classification theorem for
obligatory triple systems.  The candidate solution imports the full project;
Comparator checks that the statement and every ordinary declaration used by
its type agree with this independently compiled surface.
-/

namespace Erdos593

open scoped Cardinal

universe u v w x

namespace SimpleGraph

/-- The set of graph edges that are bridges.  The edge-membership conjunct is
included because Mathlib's endpoint-disconnection predicate `IsBridge` alone
does not assert membership in the graph. -/
def bridgeEdges {V : Type u} (G : _root_.SimpleGraph V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ G.IsBridge e}

end SimpleGraph

/-- A simple 3-uniform hypergraph with vertex type `V` and edge-index type
`E`. -/
structure TripleSystem (V : Type u) (E : Type v) where
  /-- Vertex-edge incidence. -/
  Inc : V → E → Prop
  /-- Every indexed edge contains exactly three vertices. -/
  edge_ncard : ∀ e, Set.ncard {x | Inc x e} = 3
  /-- Distinct edge indices determine distinct vertex sets. -/
  simple : Function.Injective (fun e => {x | Inc x e})

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- A point is isolated when it belongs to no hyperedge. -/
def IsIsolated (x : V) : Prop :=
  ∀ e, ¬F.Inc x e

/-- Any two distinct hyperedges of a linear triple system share at most one
point. -/
def Linear : Prop :=
  ∀ ⦃e f : E⦄ ⦃x y : V⦄, e ≠ f →
    F.Inc x e → F.Inc x f → F.Inc y e → F.Inc y f → x = y

/-- An indexed edge represented by its set of incident vertices. -/
def edgeSet (e : E) : Set V :=
  {x | F.Inc x e}

/-- A non-induced embedding of one edge-indexed triple system into another. -/
structure Embedding {V : Type u} {E : Type v} {W : Type w} {D : Type x}
    (F : TripleSystem V E) (H : TripleSystem W D) where
  /-- Injective map on vertices. -/
  vertex : V ↪ W
  /-- Choice of a host hyperedge for every source hyperedge. -/
  edge : E → D
  /-- The chosen host edge is exactly the image of the source edge. -/
  map_edge : ∀ e, vertex '' F.edgeSet e = H.edgeSet (edge e)

/-- A vertex colouring is proper when every hyperedge contains two vertices
of different colours. -/
def IsProperColoring {C : Type w} (c : V → C) : Prop :=
  ∀ e : E, ∃ x : V, F.Inc x e ∧ ∃ y : V, F.Inc y e ∧ c x ≠ c y

/-- The least cardinality of a colour type admitting a proper colouring. -/
noncomputable def chromaticCardinal : Cardinal.{u} :=
  sInf {k : Cardinal.{u} | ∃ C : Type u, #C = k ∧
    ∃ c : V → C, F.IsProperColoring c}

/-- `F` appears in `H` when there is a non-induced triple-system embedding. -/
def Appears {W : Type u} {D : Type v}
    (F : TripleSystem V E) (H : TripleSystem W D) : Prop :=
  Nonempty (F.Embedding H)

/-- A finite source is obligatory when it appears in every triple system of
uncountable chromatic cardinality in the ambient universes. -/
def IsObligatory : Prop :=
  ∀ (W : Type u) (D : Type v) [DecidableEq W]
    (H : TripleSystem W D), ℵ₀ < H.chromaticCardinal → F.Appears H

/-- Any point incident with an edge is non-isolated. -/
theorem not_isolated_of_inc {x : V} {e : E} (hxe : F.Inc x e) :
    ¬F.IsIsolated x := by
  intro hx
  exact hx e hxe

/-- The type of non-isolated points of `F`. -/
abbrev NonIsolatedPoint :=
  {x : V // ¬F.IsIsolated x}

/-- Delete all isolated points while retaining the original edge indices. -/
def isolatedReduction : TripleSystem F.NonIsolatedPoint E where
  Inc x e := F.Inc x.1 e
  edge_ncard := by
    intro e
    change Set.ncard {x : F.NonIsolatedPoint |
      (x : V) ∈ {y : V | F.Inc y e}} = 3
    rw [Set.ncard_subtype]
    have hsubset : {x : V | F.Inc x e} ⊆ {x : V | ¬F.IsIsolated x} := by
      intro x hx
      exact F.not_isolated_of_inc hx
    rw [Set.inter_eq_left.mpr hsubset]
    exact F.edge_ncard e
  simple := by
    intro e f hef
    apply F.simple
    ext x
    constructor
    · intro hxe
      let x' : F.NonIsolatedPoint := ⟨x, F.not_isolated_of_inc hxe⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mp hxe
    · intro hxf
      let x' : F.NonIsolatedPoint := ⟨x, F.not_isolated_of_inc hxf⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mpr hxf

/-- Directed point-to-edge incidence before `SimpleGraph.fromRel` symmetrizes
it. -/
def incidenceRel : V ⊕ E → V ⊕ E → Prop
  | .inl x, .inr e => F.Inc x e
  | _, _ => False

/-- The bipartite point-edge incidence (Levi) graph of a triple system. -/
def levi : _root_.SimpleGraph (V ⊕ E) :=
  _root_.SimpleGraph.fromRel F.incidenceRel

/-- Every Levi hyperedge-node is incident with an actual bridge edge. -/
def BridgeAtEveryEdge : Prop :=
  ∀ e : E, ∃ x : V,
    s(Sum.inl x, Sum.inr e) ∈ SimpleGraph.bridgeEdges F.levi

/-- Every Berge cycle has even length, expressed by divisibility by four of
the corresponding Levi-cycle length. -/
def EvenBergeCycles : Prop :=
  ∀ ⦃z : V ⊕ E⦄ (c : F.levi.Walk z z), c.IsCycle → 4 ∣ c.length

/-- The three intrinsic conditions in the finite classification: linearity, a
Levi bridge incident with every hyperedge-node, and even Berge cycles. -/
def Intrinsic : Prop :=
  F.Linear ∧ F.BridgeAtEveryEdge ∧ F.EvenBergeCycles

/-- A finite triple system is obligatory exactly when its isolated reduction
satisfies the intrinsic structural conditions. -/
theorem isObligatory_iff_isolatedReduction_intrinsic
    {V E : Type u} (F : TripleSystem V E) [Fintype V] [Fintype E] :
    F.IsObligatory ↔ F.isolatedReduction.Intrinsic := by
  sorry

end TripleSystem

end Erdos593
