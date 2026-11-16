module

public import Erdos593.FCDefs
public import Erdos593.TripleSystem.ObligatoryClassification

/-!
# Adapter to the formal-conjectures statement of Erdős Problem 593

`FormalConjectures/ErdosProblems/593.lean` in google-deepmind/formal-conjectures states
Erdős Problem 593 as the value question

`{p : Σ n : ℕ, UniformHypergraph (Fin n) 3 | p.2.IsObligatory} = erdos_593.answer`.

The namespace `FCErdos593` below reproduces the proposed upstream text of `leviGraph`,
`erdos_593.answer` and the statement `erdos_593` (upstream namespace `Erdos593`, renamed
here to avoid a clash with this project's namespace). `UniformHypergraph` and
`UniformHypergraph.IsObligatory` come from `Erdos593.FCDefs`, a verbatim copy of the
upstream definitions at commit 083f7d02c2eececd918155b2ba06981d2dd61b2f.

The proof derives the upstream statement from the registered theorem
`Erdos593.TripleSystem.isObligatory_iff_isolatedReduction_intrinsic`:

* `toTriple` and `ofTriple` translate between upstream uniform hypergraphs and this
  project's edge-indexed triple systems. They preserve proper colourings, hence chromatic
  cardinals, and appearances, hence obligatoriness (`isObligatory_iff`).
* Deleting isolated points does not change the intrinsic conditions
  (`intrinsic_isolatedReduction_iff`), because the Levi graph of the reduction is the Levi
  graph of the original system minus isolated vertices.
* For `toTriple F` the intrinsic conditions are the three conditions of the answer
  (`intrinsic_toTriple_iff`).
-/

@[expose] public section

open Cardinal Set SimpleGraph

namespace FCErdos593

/-- The Levi graph (point–edge incidence graph) of a hypergraph `H` on `V`: the bipartite graph
on `V ⊕ H.edgeSet` joining a vertex $x$ to an edge $e$ exactly when $x \in e$. -/
def leviGraph {V : Type*} {k : ℕ} (H : UniformHypergraph V k) :
    SimpleGraph (V ⊕ H.edgeSet) :=
  SimpleGraph.fromRel fun
    | .inl x, .inr e => x ∈ (e : Set V)
    | _, _ => False

/-- The finite $3$-uniform hypergraphs `H` such that
1. `H` is linear: two distinct edges share at most one vertex;
2. every edge-node of the Levi graph of `H` is incident with a bridge of the Levi graph;
3. every Berge cycle of `H` has even length. A Berge cycle of length $\ell$ is a cycle of
   length $2\ell$ in the Levi graph, so this says that every cycle of the Levi graph has
   length divisible by $4$. -/
def erdos_593.answer : Set ((n : ℕ) × UniformHypergraph (Fin n) 3) :=
  {p | p.2.edgeSet.Pairwise (fun e f ↦ (e ∩ f).Subsingleton) ∧
    (∀ e : p.2.edgeSet, ∃ x ∈ (e : Set (Fin p.1)),
      (leviGraph p.2).IsBridge s(.inl x, .inr e)) ∧
    ∀ (z : Fin p.1 ⊕ p.2.edgeSet) (c : (leviGraph p.2).Walk z z), c.IsCycle → 4 ∣ c.length}

end FCErdos593

namespace Erdos593

namespace FCAdapter

universe u v

open TripleSystem

/-! ### Pulling walks back along a graph embedding whose image contains every edge -/

section Pullback

variable {α β : Type*} {G' : _root_.SimpleGraph α} {G : _root_.SimpleGraph β}

/-- A walk of `G` starting in the image of `f` lifts to `G'` when every edge of `G` has its
endpoints in the image of `f`. -/
theorem walk_pullback (f : G' ↪g G) (hrange : ∀ u w, G.Adj u w → u ∈ Set.range f) :
    ∀ {u w : β} (p : G.Walk u w) (a : α), f a = u →
      ∃ (b : α) (q : G'.Walk a b), f b = w ∧ q.support.map f = p.support := by
  intro u w p
  induction p with
  | nil =>
    intro a ha
    exact ⟨a, .nil, ha, by simp [ha]⟩
  | cons h p ih =>
    intro a ha
    obtain ⟨c, hc⟩ := hrange _ _ h.symm
    obtain ⟨b, q, hb, hs⟩ := ih c hc
    refine ⟨b, .cons (f.map_adj_iff.mp ?_) q, hb, ?_⟩
    · rw [ha, hc]
      exact h
    · simp [hs, ha]

theorem walk_pullback_eq (f : G' ↪g G) (hrange : ∀ u w, G.Adj u w → u ∈ Set.range f)
    {a b : α} (p : G.Walk (f a) (f b)) :
    ∃ q : G'.Walk a b, q.map f.toHom = p := by
  obtain ⟨b', q, hb', hs⟩ := walk_pullback f hrange p a rfl
  obtain rfl : b' = b := f.injective hb'
  refine ⟨q, _root_.SimpleGraph.Walk.ext_support ?_⟩
  rw [_root_.SimpleGraph.Walk.support_map]
  exact hs

theorem isBridge_iff_of_embedding (f : G' ↪g G)
    (hrange : ∀ u w, G.Adj u w → u ∈ Set.range f) (a b : α) :
    G'.IsBridge s(a, b) ↔ G.IsBridge s(f a, f b) := by
  rw [_root_.SimpleGraph.isBridge_iff_forall_walk_mem_edges,
    _root_.SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  constructor
  · intro h p
    obtain ⟨q, rfl⟩ := walk_pullback_eq f hrange p
    rw [_root_.SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(a, b), h q, Sym2.map_mk _ _ _⟩
  · intro h q
    have hq := h (q.map f.toHom)
    rw [_root_.SimpleGraph.Walk.edges_map, List.mem_map] at hq
    obtain ⟨e, he, hee⟩ := hq
    have : e = s(a, b) :=
      Sym2.map.injective f.injective (hee.trans (Sym2.map_mk f a b).symm)
    rwa [← this]

theorem exists_cycle_pullback (f : G' ↪g G) (hrange : ∀ u w, G.Adj u w → u ∈ Set.range f)
    {z : β} (c : G.Walk z z) (hc : c.IsCycle) :
    ∃ (a : α) (q : G'.Walk a a), q.IsCycle ∧ q.length = c.length := by
  obtain ⟨a, rfl⟩ : z ∈ Set.range f := by
    cases c with
    | nil => exact (hc.ne_nil rfl).elim
    | cons h _ => exact hrange _ _ h
  obtain ⟨q, rfl⟩ := walk_pullback_eq f hrange c
  refine ⟨a, q, ?_, ?_⟩
  · exact (_root_.SimpleGraph.Walk.isCycle_map_iff_of_injective (f := f.toHom) f.injective).mp hc
  · rw [_root_.SimpleGraph.Walk.length_map]

end Pullback

/-! ### Deleting isolated points preserves the intrinsic conditions -/

section Isolated

variable {V : Type u} {E : Type v}

/-- The Levi graph of the isolated-point reduction embeds in the Levi graph. -/
def leviEmbedding (T : TripleSystem V E) : T.isolatedReduction.levi ↪g T.levi where
  toFun := Sum.map Subtype.val id
  inj' := Sum.map_injective.mpr ⟨Subtype.val_injective, Function.injective_id⟩
  map_rel_iff' := by
    intro a b
    rcases a with x | e <;> rcases b with y | e' <;> simp

/-- Every edge of the Levi graph has its endpoints among the non-isolated points and the
hyperedges. -/
theorem levi_adj_mem_range (T : TripleSystem V E) :
    ∀ u w, T.levi.Adj u w → u ∈ Set.range (leviEmbedding T) := by
  rintro (x | e) (y | e') h
  · simp at h
  · exact ⟨.inl ⟨x, T.not_isolated_of_inc (by simpa using h)⟩, rfl⟩
  · exact ⟨.inr e, rfl⟩
  · exact ⟨.inr e, rfl⟩

theorem mem_bridgeEdges_isolatedReduction_iff (T : TripleSystem V E)
    (x : T.NonIsolatedPoint) (e : E) :
    s(Sum.inl x, Sum.inr e) ∈ SimpleGraph.bridgeEdges T.isolatedReduction.levi ↔
      s(Sum.inl x.1, Sum.inr e) ∈ SimpleGraph.bridgeEdges T.levi := by
  have h1 : T.isolatedReduction.levi.Adj (.inl x) (.inr e) ↔ T.levi.Adj (.inl x.1) (.inr e) := by
    simp
  have h2 : T.isolatedReduction.levi.IsBridge s(.inl x, .inr e) ↔
      T.levi.IsBridge s(.inl x.1, .inr e) :=
    isBridge_iff_of_embedding (leviEmbedding T) (levi_adj_mem_range T) (.inl x) (.inr e)
  simp only [SimpleGraph.bridgeEdges, Set.mem_ofPred_eq, _root_.SimpleGraph.mem_edgeSet, h1, h2]

theorem intrinsic_isolatedReduction_iff (T : TripleSystem V E) :
    T.isolatedReduction.Intrinsic ↔ T.Intrinsic := by
  constructor
  · rintro ⟨hlin, hbr, hcyc⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e f x y hef hxe hxf hye hyf
      exact congrArg Subtype.val
        (@hlin e f ⟨x, T.not_isolated_of_inc hxe⟩ ⟨y, T.not_isolated_of_inc hye⟩
          hef hxe hxf hye hyf)
    · intro e
      obtain ⟨x, hx⟩ := hbr e
      exact ⟨x.1, (mem_bridgeEdges_isolatedReduction_iff T x e).mp hx⟩
    · intro z c hc
      obtain ⟨a, q, hq, hlen⟩ :=
        exists_cycle_pullback (leviEmbedding T) (levi_adj_mem_range T) c hc
      rw [← hlen]
      exact hcyc q hq
  · rintro ⟨hlin, hbr, hcyc⟩
    refine ⟨T.isolatedReduction_linear hlin, ?_, ?_⟩
    · intro e
      obtain ⟨x, hx⟩ := hbr e
      have hinc : T.Inc x e := by
        have hx' := hx
        obtain ⟨hadj, -⟩ := hx'
        simpa using (_root_.SimpleGraph.mem_edgeSet _).mp hadj
      exact ⟨⟨x, T.not_isolated_of_inc hinc⟩,
        (mem_bridgeEdges_isolatedReduction_iff T ⟨x, T.not_isolated_of_inc hinc⟩ e).mpr hx⟩
    · intro z c hc
      have h := hcyc (c.map (leviEmbedding T).toHom)
        ((_root_.SimpleGraph.Walk.isCycle_map_iff_of_injective (f := (leviEmbedding T).toHom)
          (leviEmbedding T).injective).mpr hc)
      rwa [_root_.SimpleGraph.Walk.length_map] at h

end Isolated

/-! ### Translation between uniform hypergraphs and triple systems -/

section Translation

variable {V : Type u}

/-- A formal-conjectures `3`-uniform hypergraph as a triple system indexed by its edges. -/
def toTriple (H : UniformHypergraph V 3) : TripleSystem V H.edgeSet where
  Inc x e := x ∈ (e : Set V)
  edge_ncard e := by
    have h := H.uniform e.1 e.2
    change Set.ncard (e : Set V) = 3
    rw [Set.ncard_def, h]
    simp
  simple := by
    intro e f h
    exact Subtype.ext (Set.ext fun x => Set.ext_iff.mp h x)

/-- A triple system as a formal-conjectures `3`-uniform hypergraph. -/
def ofTriple {D : Type v} (H : TripleSystem V D) : UniformHypergraph V 3 where
  vertexSet := Set.univ
  edgeSet := Set.range H.edgeSet
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _
  vertexSet_eq_univ := rfl
  uniform := by
    rintro _ ⟨e, rfl⟩
    have h : (H.edgeSet e).ncard = 3 := H.edge_ncard e
    have hfin : (H.edgeSet e).Finite := Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)
    rw [← hfin.cast_ncard_eq, h]

theorem isProperColoring_toTriple {C : Type*} (H : UniformHypergraph V 3) (c : V → C) :
    (toTriple H).IsProperColoring c ↔ H.IsProperColoring c :=
  ⟨fun h e he => h ⟨e, he⟩, fun h e => h e.1 e.2⟩

theorem isProperColoring_ofTriple {D : Type v} {C : Type*} (H : TripleSystem V D)
    (c : V → C) : (ofTriple H).IsProperColoring c ↔ H.IsProperColoring c := by
  constructor
  · intro h e
    exact h _ (Set.mem_range_self e)
  · rintro h _ ⟨e, rfl⟩
    exact h e

theorem chromaticCardinal_toTriple (H : UniformHypergraph V 3) :
    (toTriple H).chromaticCardinal = H.chromaticCardinal := by
  unfold TripleSystem.chromaticCardinal UniformHypergraph.chromaticCardinal
  congr 1
  ext κ
  constructor
  · rintro ⟨C, hC, c, hc⟩
    exact ⟨C, hC, c, (isProperColoring_toTriple H c).mp hc⟩
  · rintro ⟨C, hC, c, hc⟩
    exact ⟨C, hC, c, (isProperColoring_toTriple H c).mpr hc⟩

theorem chromaticCardinal_ofTriple {D : Type v} (H : TripleSystem V D) :
    (ofTriple H).chromaticCardinal = H.chromaticCardinal := by
  unfold TripleSystem.chromaticCardinal UniformHypergraph.chromaticCardinal
  congr 1
  ext κ
  constructor
  · rintro ⟨C, hC, c, hc⟩
    exact ⟨C, hC, c, (isProperColoring_ofTriple H c).mp hc⟩
  · rintro ⟨C, hC, c, hc⟩
    exact ⟨C, hC, c, (isProperColoring_ofTriple H c).mpr hc⟩

/-- The two notions of obligatoriness agree. -/
theorem isObligatory_iff [Fintype V] (F : UniformHypergraph V 3) :
    F.IsObligatory ↔ (toTriple F).IsObligatory := by
  constructor
  · intro hF X D _ H hχ
    have hχ' : ℵ₀ < (ofTriple H).chromaticCardinal := by
      rwa [chromaticCardinal_ofTriple]
    obtain ⟨φ, hφ, hsub⟩ := hF X (ofTriple H) hχ'
    have hr : ∀ e : F.edgeSet, ∃ d, H.edgeSet d = φ '' (e : Set V) :=
      fun e => hsub (Hypergraph.image_mem_edgeSet_image e.2)
    choose g hg using hr
    exact ⟨{ vertex := ⟨φ, hφ⟩, edge := g, map_edge := fun e => (hg e).symm }⟩
  · intro hT X _ H hχ
    have hχ' : ℵ₀ < (toTriple H).chromaticCardinal := by
      rwa [chromaticCardinal_toTriple]
    obtain ⟨emb⟩ := hT X H.edgeSet (toTriple H) hχ'
    refine ⟨emb.vertex, emb.vertex.injective, ?_⟩
    intro s hs
    obtain ⟨e, he, rfl⟩ := Hypergraph.mem_edgeSet_image.mp hs
    have h := emb.map_edge ⟨e, he⟩
    change (emb.vertex : V → X) '' e = ((emb.edge ⟨e, he⟩ : H.edgeSet) : Set X) at h
    rw [h]
    exact (emb.edge ⟨e, he⟩).2

theorem levi_toTriple (H : UniformHypergraph V 3) :
    (toTriple H).levi = FCErdos593.leviGraph H := by
  ext a b
  rcases a with x | e <;> rcases b with y | e' <;>
    simp [FCErdos593.leviGraph, toTriple]

/-- For `toTriple F`, the intrinsic conditions are the three conditions of the answer. -/
theorem intrinsic_toTriple_iff {n : ℕ} (F : UniformHypergraph (Fin n) 3) :
    (toTriple F).Intrinsic ↔ (⟨n, F⟩ : (n : ℕ) × UniformHypergraph (Fin n) 3) ∈
      FCErdos593.erdos_593.answer := by
  unfold TripleSystem.Intrinsic TripleSystem.BridgeAtEveryEdge TripleSystem.EvenBergeCycles
  rw [levi_toTriple]
  show _ ↔ _ ∧ _ ∧ _
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro hlin e he f hf hef x hx y hy
      exact @hlin ⟨e, he⟩ ⟨f, hf⟩ x y (fun h => hef (congrArg Subtype.val h))
        hx.1 hx.2 hy.1 hy.2
    · intro hpw e f x y hef hxe hxf hye hyf
      exact hpw e.2 f.2 (fun h => hef (Subtype.ext h))
        (show x ∈ (e : Set (Fin n)) ∩ f from ⟨hxe, hxf⟩)
        (show y ∈ (e : Set (Fin n)) ∩ f from ⟨hye, hyf⟩)
  · constructor
    · intro h e
      obtain ⟨x, hadj, hbr⟩ := h e
      refine ⟨x, ?_, hbr⟩
      simpa [FCErdos593.leviGraph] using (_root_.SimpleGraph.mem_edgeSet _).mp hadj
    · intro h e
      obtain ⟨x, hx, hbr⟩ := h e
      refine ⟨x, (_root_.SimpleGraph.mem_edgeSet _).mpr ?_, hbr⟩
      simpa [FCErdos593.leviGraph] using hx
  · exact ⟨fun h z c hc => h c hc, fun h z c hc => h z c hc⟩

end Translation

end FCAdapter

end Erdos593

namespace FCErdos593

open Erdos593 Erdos593.FCAdapter

/-- The formal-conjectures statement of Erdős Problem 593 with the answer above, derived from
the registered theorem `Erdos593.TripleSystem.isObligatory_iff_isolatedReduction_intrinsic`. -/
theorem erdos_593 :
    {p : Σ n : ℕ, UniformHypergraph (Fin n) 3 | p.2.IsObligatory} = erdos_593.answer := by
  ext ⟨n, F⟩
  have : Fintype F.edgeSet := Fintype.ofFinite _
  show F.IsObligatory ↔ _
  rw [isObligatory_iff F, TripleSystem.isObligatory_iff_isolatedReduction_intrinsic,
    intrinsic_isolatedReduction_iff, intrinsic_toTriple_iff]

end FCErdos593
