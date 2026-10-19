/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Metrization.LocallyFinite
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Basic

/-!
# Nonvacuity clients for locally finite metrization statements

The first two clients use the original discrete coproduct `Σ r : ℝ, PUnit`, with
uncountable singleton levels. The third uses the original coproduct `Σ r : ℝ, ℝ`
and its uncountable clopen component cover. Its pieces are independently metrizable
through their homeomorphisms to `ℝ`, not by inheriting ambient metrizability.

## References

The coproduct witnesses use Mathlib's sigma-space topology and component maps,
`Topology.IsEmbedding.sigmaMk` and `Topology.IsEmbedding.toHomeomorph`, to transfer
metrizability between a component and its model.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Topology

-- Repeating the whole singleton level at every natural number is allowed.
example : MetrizableSpace (Σ _ : ℝ, PUnit.{1}) := by
  let X := Σ _ : ℝ, PUnit.{1}
  let B : ℕ → X → Set X := fun _ x => {x}
  have hfin : ∀ n, LocallyFinite (B n) := by
    intro n x
    refine ⟨{x}, (isOpen_discrete _).mem_nhds (mem_singleton x), ?_⟩
    apply (finite_singleton x).subset
    rintro y ⟨z, hz, hx⟩
    have hzy : z = y := by simpa only [B, mem_singleton_iff] using hz
    have hzx : z = x := mem_singleton_iff.mp hx
    exact mem_singleton_iff.mpr (hzy.symm.trans hzx)
  have hB : IsTopologicalBasis (⋃ n, range (B n)) := by
    have heq : (⋃ n, range (B n)) = {s : Set X | ∃ x : X, s = {x}} := by
      ext s
      constructor
      · intro hs
        rcases mem_iUnion.mp hs with ⟨n, x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact mem_iUnion.mpr ⟨0, x, rfl⟩
    rw [heq]
    exact isTopologicalBasis_singletons X
  exact metrizableSpace_of_sigmaLocallyFinite_isTopologicalBasis B hB hfin

-- The converse input comes from discrete-space metrizability, independently of the first criterion.
example : ∃ B : ℕ → (Σ _ : ℝ, PUnit.{1}) → Set (Σ _ : ℝ, PUnit.{1}),
    (∀ n, LocallyFinite (B n)) ∧ IsTopologicalBasis (⋃ n, range (B n)) := by
  let : MetrizableSpace (Σ _ : ℝ, PUnit.{1}) := DiscreteTopology.metrizableSpace
  exact exists_sigmaLocallyFinite_isTopologicalBasis (Σ _ : ℝ, PUnit.{1})

-- The closed component cover supplies ambient separation and metrizability.
example : MetrizableSpace (Σ _ : ℝ, ℝ) := by
  let C : ℝ → Set (Σ _ : ℝ, ℝ) := fun r => range (Sigma.mk r)
  have hopen : ∀ r, IsOpen (C r) := fun _ => isOpen_range_sigmaMk
  have hclosed : ∀ r, IsClosed (C r) := fun _ => isClosed_range_sigmaMk
  have hfin : LocallyFinite C := by
    rintro ⟨s, a⟩
    refine ⟨C s, (hopen s).mem_nhds ⟨a, rfl⟩, ?_⟩
    apply (finite_singleton s).subset
    rintro r ⟨y, hyr, hys⟩
    rcases hyr with ⟨b, hb⟩
    rcases hys with ⟨c, hc⟩
    exact mem_singleton_iff.mpr
      ((congrArg Sigma.fst hb).trans (congrArg Sigma.fst hc).symm)
  have hcover : (⋃ r, interior (C r)) = univ := by
    apply eq_univ_iff_forall.mpr
    rintro ⟨r, a⟩
    refine mem_iUnion.mpr ⟨r, ?_⟩
    rw [(hopen r).interior_eq]
    exact ⟨a, rfl⟩
  have hmetr : ∀ r, MetrizableSpace (C r) := by
    intro r
    have hem : Topology.IsEmbedding (@Sigma.mk ℝ (fun _ : ℝ => ℝ) r) :=
      Topology.IsEmbedding.sigmaMk (σ := fun _ : ℝ => ℝ) (i := r)
    let e : ℝ ≃ₜ C r := hem.toHomeomorph
    exact e.symm.isEmbedding.metrizableSpace
  exact metrizableSpace_of_locallyFinite_isClosed_interior_cover C hfin hclosed hcover hmetr
