/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-
Provenance: definitions copied from google-deepmind/formal-conjectures at commit
083f7d02c2eececd918155b2ba06981d2dd61b2f (upstream `main` on 2026-11-16):

* `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Basic.lean` (whole body),
* `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean` (only `Finset.IsUniform`
  and `Finset.IsProperHypergraphColoring`, the two declarations `Uniform.lean` uses),
* `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Uniform.lean` (whole body).

Modifications (Apache-2.0, section 4(b)): the three files are concatenated into one module,
their imports are replaced by the Mathlib modules they need, and the unused parts of
`Finite.lean` are omitted. Declaration names, namespaces, statements, definitions and proofs
are otherwise unchanged, so `UniformHypergraph.IsObligatory` here is the predicate used by
`FormalConjectures/ErdosProblems/593.lean` at that commit.
-/
module

public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Ordinal

/-! ## From `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Basic.lean` -/

@[expose] public section

/-!
# Uniformity and weak colorings of hypergraphs

This file extends Mathlib's `Hypergraph` with finite-edge constructors, uniformity,
and weak proper colorings. Uniformity uses extended cardinality, so every edge is finite,
including at uniformity zero. Empty and singleton edges admit no weak proper coloring.
-/

namespace Hypergraph

/-- Every edge has exactly `k` vertices. -/
def IsUniform {V : Type*} (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H.edgeSet, e.encard = k

/-- A weak proper coloring gives two vertices different colors in every edge. -/
def IsProperColoring {V C : Type*} (H : Hypergraph V) (f : V → C) : Prop :=
  ∀ e ∈ H.edgeSet, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- A weak proper coloring using at most `n` colors. -/
def IsNColorable {V : Type*} (H : Hypergraph V) (n : ℕ) : Prop :=
  ∃ f : V → Fin n, H.IsProperColoring f

/-- A family of finite edges on an explicit vertex set, retaining isolated vertices. -/
def ofEdgeFamily {V : Type*} (F : Set (Finset V)) (S : Set V)
    (h : ∀ e ∈ F, (e : Set V) ⊆ S) : Hypergraph V where
  vertexSet := S
  edgeSet := {e | ∃ a ∈ F, (a : Set V) = e}
  subset_vertexSet_of_mem_edgeSet' := by
    rintro e ⟨a, ha, rfl⟩
    exact h a ha

@[simp]
theorem mem_edgeSet_ofEdgeFamily {V : Type*} {F : Set (Finset V)} {S : Set V}
    {h : ∀ e ∈ F, (e : Set V) ⊆ S} {e : Finset V} :
    (e : Set V) ∈ (ofEdgeFamily F S h).edgeSet ↔ e ∈ F := by
  simp [ofEdgeFamily]

@[simp]
theorem isUniform_ofEdgeFamily_iff {V : Type*} {F : Set (Finset V)} {S : Set V}
    {h : ∀ e ∈ F, (e : Set V) ⊆ S} {k : ℕ} :
    (ofEdgeFamily F S h).IsUniform k ↔ ∀ e ∈ F, e.card = k := by
  simp [IsUniform, ofEdgeFamily]

@[simp]
theorem isProperColoring_ofEdgeFamily_iff {V C : Type*} {F : Set (Finset V)}
    {S : Set V} {h : ∀ e ∈ F, (e : Set V) ⊆ S} {f : V → C} :
    (ofEdgeFamily F S h).IsProperColoring f ↔
      ∀ e ∈ F, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v := by
  simp [IsProperColoring, ofEdgeFamily]

/-- Every edge of a uniform hypergraph is finite. -/
theorem IsUniform.finite_edge {V : Type*} {H : Hypergraph V} {k : ℕ}
    (hH : H.IsUniform k) {e : Set V} (he : e ∈ H.edgeSet) : e.Finite :=
  Set.finite_of_encard_eq_coe (hH e he)

/-- An injective coloring is proper when every edge has at least two vertices. -/
theorem isProperColoring_of_injective {V C : Type*} {H : Hypergraph V}
    (hH : ∀ e ∈ H.edgeSet, 2 ≤ e.encard) {f : V → C}
    (hf : Function.Injective f) : H.IsProperColoring f := by
  intro e he
  obtain ⟨u, v, hu, hv, huv⟩ := Set.one_lt_encard_iff.mp
    (lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2) (hH e he))
  exact ⟨u, hu, v, hv, fun h ↦ huv (hf h)⟩

/-- An injective coloring is proper when uniformity is at least two. -/
theorem IsUniform.isProperColoring_of_injective {V C : Type*} {H : Hypergraph V}
    {k : ℕ} (hH : H.IsUniform k) (hk : 2 ≤ k) {f : V → C}
    (hf : Function.Injective f) : H.IsProperColoring f := by
  apply Hypergraph.isProperColoring_of_injective ?_ hf
  intro e he
  rw [hH e he]
  exact_mod_cast hk

end Hypergraph

/-! ## From `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean` (excerpt) -/

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- Every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- A weak proper coloring has no monochromatic edge. -/
def IsProperHypergraphColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

end Finset

/-! ## From `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Uniform.lean` -/


/-!
# Uniform hypergraphs

A `UniformHypergraph V k` extends Mathlib's `Hypergraph V` with uniformity `k`
and vertex set `Set.univ`. The vertex type includes isolated vertices.
Finite edge families use `Finset.IsUniform`;
`UniformHypergraph.ofFinset` converts them to this presentation.

The API includes complete subgraphs, maximal clique sizes, weak colorings, embeddings,
and chromatic cardinals. The chromatic cardinal is zero when no proper coloring exists.
Empty and singleton edges admit no weak proper coloring.
-/

open Cardinal Set

universe u

/-- A uniform Mathlib hypergraph whose vertex set is the entire ambient type. -/
structure UniformHypergraph (V : Type*) (k : ℕ) extends Hypergraph V where
  /-- All elements of the vertex type are vertices, including isolated ones. -/
  vertexSet_eq_univ : vertexSet = Set.univ
  /-- Every hyperedge has exactly `k` vertices. -/
  uniform : toHypergraph.IsUniform k

namespace UniformHypergraph

variable {k : ℕ}

/-- A finite uniform edge family viewed as a uniform hypergraph. -/
def ofFinset {V : Type*} (H : Finset (Finset V)) (hH : H.IsUniform k) :
    UniformHypergraph V k where
  toHypergraph := Hypergraph.ofEdgeFamily (H : Set (Finset V)) Set.univ
    (fun _ _ ↦ Set.subset_univ _)
  vertexSet_eq_univ := rfl
  uniform := Hypergraph.isUniform_ofEdgeFamily_iff.mpr hH

@[simp]
theorem mem_edgeSet_ofFinset {V : Type*} {H : Finset (Finset V)} {hH : H.IsUniform k}
    {e : Finset V} : (e : Set V) ∈ (ofFinset H hH).edgeSet ↔ e ∈ H :=
  Hypergraph.mem_edgeSet_ofEdgeFamily (h := fun _ _ ↦ Set.subset_univ _)

/-- Every `k`-element subset of `S` is an edge. -/
def IsCompleteOn {V : Type*} (H : UniformHypergraph V k) (S : Finset V) : Prop :=
  ∀ e : Finset V, e ⊆ S → e.card = k → (e : Set V) ∈ H.edgeSet

/-- The sizes of the finite maximal complete subgraphs. -/
def cliqueSizes {V : Type*} (H : UniformHypergraph V k) : Set ℕ :=
  { n | ∃ S : Finset V, Maximal (IsCompleteOn H) S ∧ S.card = n }

/-- Weak proper coloring of the underlying Mathlib hypergraph. -/
abbrev IsProperColoring {V : Type*} (H : UniformHypergraph V k) {C : Type*}
    (f : V → C) : Prop :=
  H.toHypergraph.IsProperColoring f

/-- An injective coloring is proper when every edge has at least two vertices. -/
theorem isProperColoring_of_injective {V C : Type*} (H : UniformHypergraph V k)
    (hk : 2 ≤ k) {f : V → C} (hf : Function.Injective f) : H.IsProperColoring f :=
  H.uniform.isProperColoring_of_injective hk hf

/-- The finite and possibly infinite presentations have the same proper colorings. -/
theorem isProperColoring_ofFinset_iff {V C : Type*} (H : Finset (Finset V))
    (hH : H.IsUniform k) (f : V → C) :
    (ofFinset H hH).IsProperColoring f ↔ H.IsProperHypergraphColoring f := by
  exact Hypergraph.isProperColoring_ofEdgeFamily_iff (h := fun _ _ ↦ Set.subset_univ _)

/-- The infimum of cardinalities of color types admitting a proper coloring.
The value is zero when no proper coloring exists. -/
noncomputable def chromaticCardinal {V : Type u} (H : UniformHypergraph V k) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (C : Type u), #C = κ ∧ ∃ f : V → C, H.IsProperColoring f}

/-- A proper coloring bounds the chromatic cardinal by the number of colors. -/
theorem chromaticCardinal_le {V C : Type u} (H : UniformHypergraph V k)
    {f : V → C} (hf : H.IsProperColoring f) : H.chromaticCardinal ≤ #C :=
  csInf_le' ⟨C, rfl, f, hf⟩

/-- The vertex type itself always supplies enough colors when `2 ≤ k`. -/
theorem chromaticCardinal_le_mk {V : Type u} (H : UniformHypergraph V k) (hk : 2 ≤ k) :
    H.chromaticCardinal ≤ #V :=
  H.chromaticCardinal_le (H.isProperColoring_of_injective hk Function.injective_id)

/-- An injective vertex map carrying every edge of `F` to an edge of `H`. -/
def Appears {W V : Type*} (F : UniformHypergraph W k)
    (H : UniformHypergraph V k) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧
    (F.toHypergraph.image φ).edgeSet ⊆ H.edgeSet

/-- Appearance is transitive under composition of injective vertex maps. -/
theorem Appears.trans {U W V : Type*} {F : UniformHypergraph U k}
    {G : UniformHypergraph W k} {H : UniformHypergraph V k}
    (hFG : F.Appears G) (hGH : G.Appears H) : F.Appears H := by
  obtain ⟨f, hf, hF⟩ := hFG
  obtain ⟨g, hg, hG⟩ := hGH
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  rw [← Hypergraph.image_image]
  exact (Set.image_mono hF).trans hG

/-- A weak proper coloring using at most `n` colors. -/
abbrev IsNColorable {V : Type*} (F : UniformHypergraph V k) (n : ℕ) : Prop :=
  F.toHypergraph.IsNColorable n

/-- Some hypergraph of the same uniformity and chromatic cardinal `κ` omits `F`. -/
def HasAvoidingChromaticCardinal {W : Type u} (F : UniformHypergraph W k)
    (κ : Cardinal.{u}) : Prop :=
  ∃ (V : Type u) (_ : DecidableEq V) (H : UniformHypergraph V k),
    H.chromaticCardinal = κ ∧ ¬ F.Appears H

/-- A finite uniform hypergraph is obligatory if it appears in every hypergraph of
that uniformity whose chromatic cardinal exceeds `ℵ₀`. -/
def IsObligatory {W : Type u} [Fintype W] (F : UniformHypergraph W k) : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : UniformHypergraph V k),
    ℵ₀ < H.chromaticCardinal → F.Appears H

end UniformHypergraph
