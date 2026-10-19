/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Separation.Regular

/-!
# Regular spaces with a sigma-locally-finite basis

A regular space whose open basis is the union of countably many locally finite
indexed levels is normal. Every open subset of such a space is a countable union
of closed subsets contained in it. Neither conclusion requires a separation axiom
in addition to regularity.

Local finiteness is used separately on each original indexed level, including
empty levels and repeated members. Restricting a level preserves local finiteness,
and taking closures commutes with its union. The normality argument forms
countable separating covers and applies the countable-cover separation lemma;
it does not assert local finiteness of the whole basis.

## References

These are the normality and closed-exhaustion steps in the classical
Nagata–Smirnov metrization theorem: J. Nagata, *On a necessary and sufficient
condition of metrizability* (1950), and Yu. M. Smirnov, *A necessary and sufficient
condition for metrizability of a topological space* (1951).
-/

@[expose] public section

open Set
open scoped Topology

namespace TopologicalSpace

universe u v

/-- The normality step in the Nagata–Smirnov metrization theorem: a regular space
with an open basis in countably many locally finite indexed levels is normal.
No T₀ or T₁ assumption is needed. -/
theorem normalSpace_of_sigmaLocallyFinite_isTopologicalBasis
    {X : Type u} [TopologicalSpace X] [RegularSpace X] {ι : ℕ → Type v}
    (B : ∀ n, ι n → Set X)
    (hB : IsTopologicalBasis (⋃ n, range (B n)))
    (hfin : ∀ n, LocallyFinite (B n)) : NormalSpace X := by
  classical
  have hsep : ∀ (s t : Set X), IsClosed t → Disjoint s t → HasSeparatingCover s t := by
    intro s t ht hst
    let W : ℕ → Set X := fun n =>
      ⋃ a : {a : ι n // Disjoint (closure (B n a)) t}, B n a
    refine ⟨W, ?_, ?_⟩
    · intro x hxs
      have hxt : x ∈ tᶜ := fun hxt => Set.disjoint_left.mp hst hxs hxt
      obtain ⟨V, hV, hxV, hVt⟩ :=
        hB.exists_closure_subset (ht.isOpen_compl.mem_nhds hxt)
      rcases mem_iUnion.mp hV with ⟨n, a, rfl⟩
      have ha : Disjoint (closure (B n a)) t := by
        apply Set.disjoint_left.mpr
        intro y hy hyt
        exact hVt hy hyt
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨a, ha⟩, hxV⟩⟩
    · intro n
      constructor
      · exact isOpen_iUnion fun a =>
          hB.isOpen (mem_iUnion.mpr ⟨n, a.val, rfl⟩)
      · have hloc : LocallyFinite
            (fun a : {a : ι n // Disjoint (closure (B n a)) t} => B n a) :=
          (hfin n).comp_injective Subtype.val_injective
        change Disjoint
          (closure (⋃ a : {a : ι n // Disjoint (closure (B n a)) t}, B n a)) t
        rw [hloc.closure_iUnion]
        apply Set.disjoint_left.mpr
        intro x hx hxt
        rcases mem_iUnion.mp hx with ⟨a, hxa⟩
        exact Set.disjoint_left.mp a.property hxa hxt
  refine ⟨?_⟩
  intro s t hs ht hst
  exact hasSeparatingCovers_iff_separatedNhds.mp
    ⟨hsep s t ht hst, hsep t s hs hst.symm⟩

/-- The closed-exhaustion step in the Nagata–Smirnov metrization theorem:
every open set in a regular space with a sigma-locally-finite basis is a
countable union of closed subsets contained in it. The closed sets need not
form an increasing sequence. -/
theorem exists_isClosed_iUnion_eq_of_sigmaLocallyFinite_isTopologicalBasis
    {X : Type u} [TopologicalSpace X] [RegularSpace X] {ι : ℕ → Type v}
    (B : ∀ n, ι n → Set X)
    (hB : IsTopologicalBasis (⋃ n, range (B n)))
    (hfin : ∀ n, LocallyFinite (B n)) (U : Set X) (hU : IsOpen U) :
    ∃ C : ℕ → Set X, (∀ k, IsClosed (C k)) ∧
      (∀ k, C k ⊆ U) ∧ (⋃ k, C k) = U := by
  classical
  let C : ℕ → Set X := fun n =>
    ⋃ a : {a : ι n // closure (B n a) ⊆ U}, closure (B n a)
  refine ⟨C, ?_, ?_, ?_⟩
  · intro n
    have hloc : LocallyFinite
        (fun a : {a : ι n // closure (B n a) ⊆ U} => closure (B n a)) :=
      (hfin n).closure.comp_injective Subtype.val_injective
    exact hloc.isClosed_iUnion fun _ => isClosed_closure
  · intro n x hx
    rcases mem_iUnion.mp hx with ⟨a, hxa⟩
    exact a.property hxa
  · apply Subset.antisymm
    · intro x hx
      rcases mem_iUnion.mp hx with ⟨n, hx⟩
      rcases mem_iUnion.mp hx with ⟨a, hxa⟩
      exact a.property hxa
    · intro x hx
      obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_closure_subset (hU.mem_nhds hx)
      rcases mem_iUnion.mp hV with ⟨n, a, rfl⟩
      exact mem_iUnion.mpr
        ⟨n, mem_iUnion.mpr ⟨⟨a, hVU⟩, subset_closure hxV⟩⟩

end TopologicalSpace
