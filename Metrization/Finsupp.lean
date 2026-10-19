/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Lp.Finsupp
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.LocallyFinite

/-!
# Continuity of locally finite finite-support maps

A continuous family of coordinates with locally finite nonzero loci defines a continuous map
into the finitely supported functions with their ℓ¹ pseudometric. Near each point,
local finiteness expresses the distance as a fixed finite sum of coordinate distances.

## References

For real-valued coordinates, this is the finite-support continuity step in the
Nagata–Smirnov metrization argument. The metric is the finite-support ℓᵖ
pseudometric from Mathlib's `Analysis.Normed.Lp.Finsupp` module.
-/

@[expose] public section

open Set Filter
open scoped BigOperators Topology

universe u v w

/-- The exponent one satisfies the bound required by the finite-support ℓᵖ pseudometric. -/
@[instance] theorem fact_one_le_one_nnreal : Fact ((1 : NNReal) ≤ 1) :=
  ⟨le_rfl⟩

namespace LocallyFinite

/-- Continuous coordinates whose nonzero loci form a locally finite family give a continuous
finite-support map for the `WithLp 1` pseudometric. No additive structure on the
coordinate space is required. -/
theorem continuous_toLp_one_ofSupportFinite
    {X : Type u} {ι : Type v} {E : Type w}
    [TopologicalSpace X] [Zero E] [PseudoMetricSpace E]
    {f : ι → X → E} (hl : LocallyFinite fun i => Function.support (f i))
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => WithLp.toLp ((1 : NNReal) : ENNReal)
      (Finsupp.ofSupportFinite (fun i => f i x)
        (show (Function.support (fun i => f i x)).Finite from hl.point_finite x))) := by
  classical
  let F : X → WithLp ((1 : NNReal) : ENNReal) (ι →₀ E) := fun x =>
    WithLp.toLp _ (Finsupp.ofSupportFinite (fun i => f i x)
      (show (Function.support (fun i => f i x)).Finite from hl.point_finite x))
  change Continuous F
  apply continuous_iff_continuousAt.2
  intro x
  obtain ⟨t, ht, hfin⟩ := hl x
  let s : Finset ι := hfin.toFinset
  have hzero : ∀ y ∈ t, ∀ i ∉ s, f i y = 0 := by
    intro y hy i hi
    by_contra hne
    exact hi (hfin.mem_toFinset.mpr ⟨y, hne, hy⟩)
  have hdist : ∀ y ∈ t, dist (F y) (F x) = ∑ i ∈ s, dist (f i y) (f i x) := by
    intro y hy
    have hsupp : ((F y).ofLp.zipWith dist (dist_self _) (F x).ofLp).support ⊆ s := by
      intro i hi
      by_contra his
      have hz : ((F y).ofLp.zipWith dist (dist_self _) (F x).ofLp) i = 0 := by
        change dist (f i y) (f i x) = 0
        rw [hzero y hy i his, hzero x (mem_of_mem_nhds ht) i his, dist_self]
      exact (Finsupp.mem_support_iff.mp hi) hz
    rw [Finsupp.dist_def]
    simp only [NNReal.coe_one, inv_one, Real.rpow_one]
    exact Finsupp.sum_of_support_subset _ hsupp _ (by intro i hi; rfl)
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hsum : Tendsto (fun y => ∑ i ∈ s, dist (f i y) (f i x)) (𝓝 x) (𝓝 0) := by
    have hcont : Continuous (fun y => ∑ i ∈ s, dist (f i y) (f i x)) :=
      continuous_finsetSum s (fun i _ => (hf i).dist continuous_const)
    have hx : Tendsto (fun y => ∑ i ∈ s, dist (f i y) (f i x))
        (𝓝 x) (𝓝 (∑ i ∈ s, dist (f i x) (f i x))) := hcont.continuousAt
    simpa only [dist_self, Finset.sum_const_zero] using hx
  apply hsum.congr'
  filter_upwards [ht] with y hy using (hdist y hy).symm

end LocallyFinite
