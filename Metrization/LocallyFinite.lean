/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Metrization.Finsupp
public import Metrization.RegularBasis
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UrysohnsLemma

/-!
# Metrizability and locally finite families

The sigma-locally-finite basis criterion, its metric converse,
and the closed metrizable neighbourhood-cover criterion.
All statements concern the given topology. `IsTopologicalBasis` already entails
openness of its members; the level and cover indices need not be countable.

## References

The basis criterion and its converse are the classical Nagata–Smirnov metrization
theorem. The converse uses metric paracompactness; the closed-neighbourhood
corollary assembles an ambient basis from bases of the pieces. The formulations
use Mathlib's `TopologicalSpace.IsTopologicalBasis`, `LocallyFinite` and
`TopologicalSpace.MetrizableSpace` APIs.
-/

@[expose] public section

open Set

namespace TopologicalSpace

universe u v w

open scoped Topology NNReal ENNReal BigOperators in
/-- The Nagata–Smirnov metrization criterion: a T₃ space with a basis in countably many
locally finite indexed levels is metrizable.
Local finiteness counts the original indices, including repetitions. -/
theorem metrizableSpace_of_sigmaLocallyFinite_isTopologicalBasis
    {X : Type u} [TopologicalSpace X] [T3Space X] {ι : ℕ → Type v}
    (B : ∀ n, ι n → Set X)
    (hB : IsTopologicalBasis (⋃ n, range (B n)))
    (hfin : ∀ n, LocallyFinite (B n)) : MetrizableSpace X := by
  classical
  let : NormalSpace X :=
    normalSpace_of_sigmaLocallyFinite_isTopologicalBasis B hB hfin
  have hopen : ∀ n a, IsOpen (B n a) := fun n a =>
    hB.isOpen (mem_iUnion.mpr ⟨n, mem_range_self a⟩)
  have hexhaust : ∀ n a, ∃ C : ℕ → Set X,
      (∀ m, IsClosed (C m)) ∧ (∀ m, C m ⊆ B n a) ∧ (⋃ m, C m) = B n a := by
    intro n a
    exact exists_isClosed_iUnion_eq_of_sigmaLocallyFinite_isTopologicalBasis
      B hB hfin (B n a) (hopen n a)
  choose C hCclosed hCsub hCunion using hexhaust
  have hury : ∀ n a m, ∃ f : C(X, ℝ),
      EqOn f 0 (B n a)ᶜ ∧ EqOn f 1 (C n a m) := by
    intro n a m
    have hd : Disjoint (B n a)ᶜ (C n a m) := by
      refine disjoint_left.mpr ?_
      intro x hx hxC
      exact hx (hCsub n a m hxC)
    obtain ⟨f, hfzero, hfone, -⟩ := exists_continuous_zero_one_of_isClosed
      (hopen n a).isClosed_compl (hCclosed n a m) hd
    exact ⟨f, hfzero, hfone⟩
  choose ρ hρzero hρone using hury
  have hρfin : ∀ n m,
      LocallyFinite (fun a : ι n => Function.support (fun x => ρ n a m x)) := by
    intro n m
    refine (hfin n).subset ?_
    intro a x hx
    by_contra hxB
    exact hx (hρzero n a m hxB)
  have : Fact (1 ≤ (1 : ℝ≥0)) := ⟨le_rfl⟩
  -- The countable-product metric has exactly the product uniformity.
  let : MetricSpace
      (∀ nm : ℕ × ℕ, WithLp ((1 : ℝ≥0) : ℝ≥0∞) (ι nm.1 →₀ ℝ)) :=
    PiCountable.metricSpace
  let Φ : X → ∀ nm : ℕ × ℕ,
      WithLp ((1 : ℝ≥0) : ℝ≥0∞) (ι nm.1 →₀ ℝ) := fun x nm =>
    WithLp.toLp ((1 : ℝ≥0) : ℝ≥0∞)
      (Finsupp.ofSupportFinite (fun a => ρ nm.1 a nm.2 x)
        (show (Function.support (fun a => ρ nm.1 a nm.2 x)).Finite from
          (hρfin nm.1 nm.2).point_finite x))
  have hΦ : Continuous Φ := by
    apply continuous_pi
    intro nm
    exact (hρfin nm.1 nm.2).continuous_toLp_one_ofSupportFinite
      (fun a => (ρ nm.1 a nm.2).continuous)
  -- A coefficient is 1-Lipschitz for the finite-support ℓ¹ metric.
  have heval : ∀ n (a : ι n),
      Continuous (fun z : WithLp ((1 : ℝ≥0) : ℝ≥0∞) (ι n →₀ ℝ) => z.ofLp a) := by
    intro n a
    have hlip : LipschitzWith 1
        (fun z : WithLp ((1 : ℝ≥0) : ℝ≥0∞) (ι n →₀ ℝ) => z.ofLp a) := by
      apply LipschitzWith.mk_one
      intro f g
      rw [Finsupp.dist_def]
      simp only [NNReal.coe_one, inv_one, Real.rpow_one]
      let d : ι n →₀ ℝ := f.ofLp.zipWith dist (dist_self _) g.ofLp
      change d a ≤ ∑ b ∈ d.support, d b
      by_cases ha : a ∈ d.support
      · exact Finset.single_le_sum
          (fun b _ => show (0 : ℝ) ≤ dist (f.ofLp b) (g.ofLp b) from dist_nonneg) ha
      · rw [Finsupp.notMem_support_iff.mp ha]
        exact Finset.sum_nonneg
          (fun b _ => show (0 : ℝ) ≤ dist (f.ofLp b) (g.ofLp b) from dist_nonneg)
    exact hlip.continuous
  have hind : Topology.IsInducing Φ := by
    apply Topology.isInducing_iff_nhds.mpr
    intro x
    apply le_antisymm
    · exact hΦ.continuousAt.le_comap
    · intro U hU
      obtain ⟨V, hVB, hxV, hVU⟩ := hB.mem_nhds_iff.mp hU
      rcases mem_iUnion.mp hVB with ⟨n, a, rfl⟩
      have hxC : x ∈ ⋃ m, C n a m := by
        rw [hCunion n a]
        exact hxV
      obtain ⟨m, hxm⟩ := mem_iUnion.mp hxC
      let W : Set (∀ nm : ℕ × ℕ,
          WithLp ((1 : ℝ≥0) : ℝ≥0∞) (ι nm.1 →₀ ℝ)) :=
        {z | (1 / 2 : ℝ) < (z (n, m)).ofLp a}
      have hW : IsOpen W :=
        isOpen_lt continuous_const ((heval n a).comp (continuous_apply (n, m)))
      refine Filter.mem_comap.mpr ⟨W, hW.mem_nhds ?_, ?_⟩
      · change (1 / 2 : ℝ) < ρ n a m x
        rw [hρone n a m hxm]
        norm_num
      · intro y hy
        apply hVU
        by_contra hyB
        change (1 / 2 : ℝ) < ρ n a m y at hy
        have hyzero : ρ n a m y = 0 := hρzero n a m hyB
        rw [hyzero] at hy
        norm_num at hy
  exact hind.isEmbedding.metrizableSpace

/-- The converse direction of the Nagata–Smirnov metrization theorem: a metrizable space
has a point-indexed basis in countably many locally finite levels. -/
theorem exists_sigmaLocallyFinite_isTopologicalBasis
    (X : Type u) [TopologicalSpace X] [MetrizableSpace X] :
    ∃ B : ℕ → X → Set X, (∀ n, LocallyFinite (B n)) ∧
      IsTopologicalBasis (⋃ n, range (B n)) := by
  classical
  let : MetricSpace X := metrizableSpaceMetric X
  have hrefine : ∀ n : ℕ, ∃ R : X → Set X,
      (∀ c, IsOpen (R c)) ∧ (⋃ c, R c) = univ ∧ LocallyFinite R ∧
        ∀ c, R c ⊆ Metric.ball c ((1 / 2 : ℝ) ^ n) := by
    intro n
    refine precise_refinement (fun c : X => Metric.ball c ((1 / 2 : ℝ) ^ n))
      (fun _ => Metric.isOpen_ball) ?_
    exact iUnion_eq_univ_iff.mpr fun x =>
      ⟨x, Metric.mem_ball_self (pow_pos one_half_pos n)⟩
  choose B hopen hcover hfin hsub using hrefine
  refine ⟨B, hfin, isTopologicalBasis_of_isOpen_of_nhds ?_ ?_⟩
  · intro U hU
    rcases mem_iUnion.mp hU with ⟨n, c, rfl⟩
    exact hopen n c
  · intro x U hx hU
    rcases Metric.isOpen_iff.mp hU x hx with ⟨r, hr, hball⟩
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hr)
      (one_half_lt_one : (1 / 2 : ℝ) < 1)
    obtain ⟨c, hc⟩ := iUnion_eq_univ_iff.mp (hcover n) x
    refine ⟨B n c, mem_iUnion.mpr ⟨n, c, rfl⟩, hc, ?_⟩
    intro y hy
    apply hball
    apply Metric.mem_ball.mpr
    calc
      dist y x ≤ dist y c + dist x c := dist_triangle_right _ _ _
      _ < (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n :=
        add_lt_add (Metric.mem_ball.mp (hsub n c hy)) (Metric.mem_ball.mp (hsub n c hc))
      _ < r / 2 + r / 2 := add_lt_add hn hn
      _ = r := add_halves r

open scoped Topology

/-- The closed-neighbourhood-cover corollary of the Nagata–Smirnov criterion: a locally finite
closed cover by metrizable neighbourhoods makes the ambient space metrizable. Each piece has
its original subtype topology; no ambient separation is assumed. -/
theorem metrizableSpace_of_locallyFinite_isClosed_interior_cover
    {X : Type u} [TopologicalSpace X] {ι : Type w} (C : ι → Set X)
    (hfin : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : (⋃ i, interior (C i)) = univ)
    (hmetr : ∀ i, MetrizableSpace (C i)) : MetrizableSpace X := by
  classical
  let : ∀ i, MetrizableSpace (C i) := hmetr
  have hlocal : ∀ x : X, ∃ i, x ∈ interior (C i) := by
    intro x
    exact mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  -- An inseparable pair belongs to a common metrizable piece.
  let : T0Space X := T0Space.of_cover (by
    intro x y hxy
    obtain ⟨i, hxi⟩ := hlocal x
    exact ⟨C i, interior_subset hxi,
      interior_subset ((hxy.mem_open_iff isOpen_interior).mp hxi), inferInstance⟩)
  -- Closed relative neighbourhoods are closed ambient neighbourhoods at interior points.
  let : RegularSpace X := RegularSpace.of_exists_mem_nhds_isClosed_subset (by
    intro x s hs
    obtain ⟨i, hxi⟩ := hlocal x
    let x' : C i := ⟨x, interior_subset hxi⟩
    have hs' : ((↑) : C i → X) ⁻¹' s ∈ 𝓝 x' :=
      continuous_subtype_val.continuousAt hs
    obtain ⟨t, ht, htc, hts⟩ := exists_mem_nhds_isClosed_subset hs'
    refine ⟨((↑) : C i → X) '' t, ?_,
      (hclosed i).isClosedMap_subtype_val t htc, ?_⟩
    · apply Filter.image_coe_mem_of_mem_comap (mem_interior_iff_mem_nhds.mp hxi)
      simpa only [x', nhds_subtype_eq_comap] using ht
    · rintro y ⟨z, hz, rfl⟩
      exact hts hz)
  choose B hBfin hBbasis using fun i => exists_sigmaLocallyFinite_isTopologicalBasis (C i)
  let G : ℕ → (Σ i, C i) → Set X := fun n a =>
    ((↑) '' B a.1 n a.2) ∩ interior (C a.1)
  -- Closedness extends relative local finiteness to all ambient points.
  have himagefin : ∀ i n, LocallyFinite (fun a : C i => ((↑) : C i → X) '' B i n a) := by
    intro i n x
    by_cases hx : x ∈ C i
    · obtain ⟨t, ht, htf⟩ := hBfin i n ⟨x, hx⟩
      have ht' : t ∈ Filter.comap ((↑) : C i → X) (𝓝 x) := by
        simpa only [nhds_subtype_eq_comap] using ht
      obtain ⟨s, hs, hst⟩ := Filter.mem_comap.mp ht'
      refine ⟨s, hs, htf.subset ?_⟩
      rintro a ⟨y, ⟨z, hz, rfl⟩, hys⟩
      exact ⟨z, hz, hst hys⟩
    · refine ⟨(C i)ᶜ, (hclosed i).isOpen_compl.mem_nhds hx, ?_⟩
      apply (finite_empty : (∅ : Set (C i)).Finite).subset
      rintro a ⟨y, ⟨z, hz, rfl⟩, hy⟩
      exact False.elim (hy z.property)
  have hGpiece : ∀ i n, LocallyFinite (fun a : C i => G n ⟨i, a⟩) := by
    intro i n
    exact (himagefin i n).subset fun _ => inter_subset_left
  have hGfin : ∀ n, LocallyFinite (G n) := by
    intro n x
    obtain ⟨N, hNx, hNF⟩ := hfin x
    choose H hHx hHfin using fun i => hGpiece i n x
    refine ⟨N ∩ ⋂ i ∈ {i | (C i ∩ N).Nonempty}, H i,
      Filter.inter_mem hNx ((Filter.biInter_mem hNF).mpr fun i _ => hHx i), ?_⟩
    have hpairs :
        (⋃ i ∈ {i | (C i ∩ N).Nonempty},
          Sigma.mk i '' {a : C i | (G n ⟨i, a⟩ ∩ H i).Nonempty}).Finite :=
      hNF.biUnion fun i _ => (hHfin i).image (Sigma.mk i)
    apply hpairs.subset
    rintro ⟨i, a⟩ ⟨y, hyG, hyN, hyH⟩
    have hi : i ∈ {i | (C i ∩ N).Nonempty} :=
      ⟨y, interior_subset hyG.2, hyN⟩
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi,
      ⟨a, ⟨y, hyG, mem_iInter.mp (mem_iInter.mp hyH i) hi⟩, rfl⟩⟩⟩
  have hGopen : ∀ n a, IsOpen (G n a) := by
    rintro n ⟨i, a⟩
    have hrel : IsOpen (B i n a) :=
      (hBbasis i).isOpen (mem_iUnion.mpr ⟨n, a, rfl⟩)
    obtain ⟨H, hHo, hH⟩ := Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range hrel
    change IsOpen ((((↑) : C i → X) '' B i n a) ∩ interior (C i))
    rw [hH, Subtype.range_coe, inter_assoc, inter_eq_self_of_subset_right interior_subset]
    exact hHo.inter isOpen_interior
  have hGbasis : IsTopologicalBasis (⋃ n, range (G n)) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      obtain ⟨n, a, rfl⟩ := mem_iUnion.mp hU
      exact hGopen n a
    · intro x U hx hU
      obtain ⟨i, hxi⟩ := hlocal x
      let x' : C i := ⟨x, interior_subset hxi⟩
      have hxU : x' ∈ ((↑) : C i → X) ⁻¹' U := hx
      obtain ⟨V, hV, hxV, hVU⟩ := (hBbasis i).exists_subset_of_mem_open hxU
        (hU.preimage continuous_subtype_val)
      obtain ⟨n, a, rfl⟩ := mem_iUnion.mp hV
      refine ⟨G n ⟨i, a⟩, mem_iUnion.mpr ⟨n, ⟨i, a⟩, rfl⟩,
        ⟨⟨x', hxV, rfl⟩, hxi⟩, ?_⟩
      rintro y ⟨⟨z, hz, rfl⟩, _⟩
      exact hVU hz
  exact metrizableSpace_of_sigmaLocallyFinite_isTopologicalBasis G hGbasis hGfin

end TopologicalSpace
