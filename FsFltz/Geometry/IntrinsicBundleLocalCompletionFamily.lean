import FsFltz.Geometry.IntrinsicBundleLocalParameter
import FsFltz.Geometry.IntrinsicBundleCompletionTransition
import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas
import FsFltz.Geometry.IntrinsicCompletionCorrespondence

/-!
# Joint local completions on the original compact bundle atlas

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158;
`def:chain`, lines 163–199; `def:maslov`, lines 225–232; and `sec:lean`,
lines 788–814. A chart and an actual parameter determine a relative open
neighborhood with a joint completed-family realization. The endpoint-safe
cutoff, the collar quotient, its mixed germs and its primitive are constructed
from the original compact bundle's data. Canonical slice comparisons retain
the independently selected original-chart completions.

Smoothness of the transported total overlaps and descent of a preselected
canonical-square section remain separate foundations. No target theorem is
asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- Retained geometric output of one native joint completion construction.
The total atlas is the actual interior/cylinder atlas determined by these
collars and their produced real mixed germs. -/
structure NativeCompletionFamily (α : Parameter → Form k M 1) where
  width : ℝ
  width_pos : 0 < width
  collar : Parameter → ℝ × IntrinsicBoundary.Point k M → M
  embedding : ∀ t, IsOpenEmbedding
    (fun p : Half width (IntrinsicBoundary.Point k M) => collar t p.val)
  smooth : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
    (collar t) (Half width (IntrinsicBoundary.Point k M))
  boundary : ∀ t (p : Half width (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (collar t p.val) ↔ p.val.1 = 0
  inverse : ∀ t p, p ∈ Half width (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (collar t p) ∧
        ∀ᶠ q in 𝓝[Half width (IntrinsicBoundary.Point k M)] p, g (collar t q) = q
  zero : ∀ t (b : IntrinsicBoundary.Point k M), collar t (0, b) = b.val
  joint : IsOpenEmbedding (totalCollar
    (fun t (p : Half width (IntrinsicBoundary.Point k M)) => collar t p.val))
  mixed : HasRealMixedGerms (δ := width) collar
  ode : ∀ t b, IsMIntegralCurveOn (fun s => collar t (s, b))
    (fun x => -liouvilleVector (α t) (exteriorDerivative (α t)) x) (Ico 0 width)
  primitive : ∀ t, (completionManifold width_pos (collar t) (embedding t) (smooth t)
    (boundary t) (inverse t) (zero t)).Form 1
  primitive_smooth : ∀ t, (completionManifold width_pos (collar t) (embedding t) (smooth t)
    (boundary t) (inverse t) (zero t)).IsSmoothForm (primitive t)
  primitive_native : ∀ t,
    letI := completionChartedSpace width_pos (collar t) (embedding t) (boundary t) (zero t)
    (fun x => (primitive t (original
      (fun p : Half width (IntrinsicBoundary.Point k M) => collar t p.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun p : Half width (IntrinsicBoundary.Point k M) => collar t p.val)) x)) = α t
  primitive_cylinder : ∀ t,
    (bandManifold width (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold width_pos (collar t) (embedding t) (smooth t)
        (boundary t) (inverse t) (zero t))
      (cylinder (fun p : Half width (IntrinsicBoundary.Point k M) => collar t p.val))
      (primitive t) = cylinderPrimitive width (α t)
  nondegenerate : ∀ t x,
    (completionManifold width_pos (collar t) (embedding t) (smooth t)
      (boundary t) (inverse t) (zero t)).Nondegenerate
      ((completionManifold width_pos (collar t) (embedding t) (smooth t)
        (boundary t) (inverse t) (zero t)).exteriorDerivative (primitive t)) x
  flows : ∀ t, Nonempty (CompleteLiouvilleFlow
    (completionManifold width_pos (collar t) (embedding t) (smooth t)
      (boundary t) (inverse t) (zero t))
    ((completionManifold width_pos (collar t) (embedding t) (smooth t)
      (boundary t) (inverse t) (zero t)).liouvilleVector (primitive t)))
  cylinder_family : (bandManifold width (IntrinsicBoundary.smoothManifold k M)).IsSmoothIntervalFormFamily
    (fun t => (bandManifold width (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold width_pos (collar t) (embedding t) (smooth t)
        (boundary t) (inverse t) (zero t))
      (cylinder (fun p : Half width (IntrinsicBoundary.Point k M) => collar t p.val)) (primitive t))

namespace NativeCompletionFamily

variable {α : Parameter → Form k M 1}

abbrev patches (F : NativeCompletionFamily α) :=
  fun t (p : Half F.width (IntrinsicBoundary.Point k M)) => F.collar t p.val

abbrev slice (F : NativeCompletionFamily α) (t : Parameter) :=
  completionManifold F.width_pos (F.collar t) (F.embedding t) (F.smooth t)
    (F.boundary t) (F.inverse t) (F.zero t)

abbrev total (F : NativeCompletionFamily α) := TotalSpace F.patches

/-- The local joint realization uses the original attachment topology. -/
@[instance_reducible]
def totalCharts (F : NativeCompletionFamily α) :
    ChartedSpace (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) F.total :=
  totalFamilyChartedSpace F.width_pos F.collar F.zero F.joint

/-- Real mixed germs construct the total smooth atlas, at both endpoints. -/
theorem total_isManifold (F : NativeCompletionFamily α) :
    letI := F.totalCharts
    IsManifold (familyModel (k + 1)) ∞ F.total :=
  totalFamily_isManifold F.width_pos F.collar F.boundary F.zero F.joint F.mixed

theorem total_t2Space (F : NativeCompletionFamily α) : T2Space F.total :=
  t2Space_totalSpace F.width_pos F.patches F.joint

theorem total_secondCountable (F : NativeCompletionFamily α) : SecondCountableTopology F.total :=
  secondCountableTopology_totalSpace F.width_pos F.patches F.zero F.joint

theorem smooth_totalInterior (F : NativeCompletionFamily α) :
    letI := F.totalCharts
    ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (totalInterior F.patches) :=
  contMDiff_totalInterior F.width_pos F.collar F.boundary F.zero F.joint F.mixed

theorem smooth_totalCylinder (F : NativeCompletionFamily α) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) F.width
    letI := F.totalCharts
    ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (totalCylinder F.patches) :=
  contMDiff_totalCylinder F.width_pos F.collar F.boundary F.zero F.joint F.mixed

theorem smooth_parameter (F : NativeCompletionFamily α) :
    letI := F.totalCharts
    ContMDiff (familyModel (k + 1)) (𝓡∂ 1) ∞ (parameter F.patches) :=
  contMDiff_parameter F.width_pos F.collar F.boundary F.zero F.joint F.mixed

end NativeCompletionFamily
end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle
open IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- A constructed realization on a relative neighborhood in an original
compact chart. The cutoff auxiliary family agrees with the chart primitive
literally on `base`; no global compact trivialization is selected. -/
structure LocalCompletionFamily (P : BundlePrimitiveData (k := k) (M := M) E)
    (c : OriginalCompactChart (k := k) (M := M) (E := E)) (t : Parameter) where
  reparam : Parameter → Parameter
  real_reparam : ℝ → ℝ
  real_smooth : ContDiff ℝ ∞ real_reparam
  real_agrees : ∀ s, (reparam s).val = real_reparam s.val
  reparam_mem : ∀ s, reparam s ∈ c.val.baseSet
  base : Set Parameter
  base_open : IsOpen base
  base_mem : t ∈ base
  base_subset : base ⊆ c.val.baseSet
  reparam_eq : ∀ s ∈ base, reparam s = s
  source_smooth : IsLocallyExtendibleFormFamily (fun s => P.form c (reparam s))
  native : NativeCompletionFamily (fun s => P.form c (reparam s))

namespace LocalCompletionFamily

variable {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

/-- Original outwardness fixes the sign of the actual chart's native normal. -/
theorem negative_normal (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter) (b : IntrinsicBoundary.Point k M) :
    (show Model (k + 1) from chartTangentMap (IntrinsicBoundary.chartAt b).ambient b.val
      (liouvilleVector (P.form c (F.reparam s))
        (exteriorDerivative (P.form c (F.reparam s))) b.val)) 0 < 0 := by
  obtain ⟨rho, beta, hz, hs, hr, hbeta, hag, hpos⟩ :=
    L.outward c (F.reparam s) (F.reparam_mem s) b
  have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
    have h := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
  exact (outward_iff_negative_normal_of_localDefiningFunction
    (IntrinsicBoundary.chartAt b).mem_atlas hx b.property rho hz hs hr hbeta hag
    (liouvilleVector (P.form c (F.reparam s))
      (exteriorDerivative (P.form c (F.reparam s))) b.val)).mp hpos

theorem normal_outward (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter) (b : IntrinsicBoundary.Point k M) :
    0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
      (normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
      (liouvilleVector (P.form c (F.reparam s))
        (exteriorDerivative (P.form c (F.reparam s))) b.val)) := by
  have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
    have h := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
  rw [normalDefiningFunction_derivative (IntrinsicBoundary.chartAt b).mem_atlas hx]
  exact neg_pos.mpr (F.negative_normal L s b)

/-- The constructed family primitive is retained in the compact domain
on the very same quotient. Its outwardness is proved from the source law. -/
def sliceLiouville (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter) :
    LiouvilleStructure (compactDomain F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
      (F.native.inverse s) (F.native.zero s)) :=
  liouvilleStructure F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
    (F.native.inverse s) (F.native.zero s) (P.form c (F.reparam s))
    (L.nondegenerate c (F.reparam s) (F.reparam_mem s)) (F.native.primitive s)
    (F.native.primitive_smooth s) (F.native.primitive_native s) (F.native.nondegenerate s)
    (F.negative_normal L s)

/-- The native presentation uses the retained joint collar quotient and
the retained primitive, rather than selecting another completion. -/
def sliceNativePresentation (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter) :
    NativeLiouvillePresentation (P.form c (F.reparam s)) :=
  nativeLiouvillePresentation F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
    (F.native.inverse s) (F.native.zero s) (P.form c (F.reparam s))
    (F.source_smooth.slice s) (L.nondegenerate c (F.reparam s) (F.reparam_mem s))
    (F.normal_outward L s) (F.native.ode s) (F.sliceLiouville L s)
    (F.native.primitive_native s)

/-- The completion inclusion is identity on the same quotient; its field
and complete flow are determined by the same retained primitive. -/
def sliceCompletion (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter) :
    Completion (F.sliceNativePresentation L s).domain :=
  completion F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
    (F.native.inverse s) (F.native.zero s) (P.form c (F.reparam s))
    (F.source_smooth.slice s) (F.sliceLiouville L s) (F.native.nondegenerate s)
    (F.native.primitive_cylinder s)

/-- The auxiliary slice primitive is literally the original compact chart
primitive on the retained relative neighborhood. -/
theorem primitive_native_on_base (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base) :
    letI := completionChartedSpace F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
    (fun x => (F.native.primitive s (original (F.native.patches s) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original (F.native.patches s)) x)) =
      P.form c s := by
  simpa only [F.reparam_eq s hs] using F.native.primitive_native s

/-- Produced strict comparison with an independently constructed original
chart completion. The source is always the retained local-family quotient. -/
structure SliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s u : Parameter) (hu : u ∈ c.val.baseSet) where
  equiv : (F.sliceCompletion L s).ambient.manifold.SmoothEquiv
    (L.chartCompletion c u hu).ambient.manifold
  boundary : (F.sliceNativePresentation L s).domain.domain.boundary.SmoothEquiv
    (L.chartNativePresentation c u hu).domain.domain.boundary
  primitive : (F.sliceCompletion L s).ambient.manifold.pullback
    (L.chartCompletion c u hu).ambient.manifold equiv
    (L.chartCompletion c u hu).ambient.primitive = (F.sliceCompletion L s).ambient.primitive
  compact : ∀ x, equiv (original (F.native.patches s) x) =
    (L.chartCompletion c u hu).inclusion.map
      ((L.chartNativePresentation c u hu).localized.inclusion x)
  compact_inverse : ∀ x, equiv.symm ((L.chartCompletion c u hu).inclusion.map
      ((L.chartNativePresentation c u hu).localized.inclusion x)) = original (F.native.patches s) x
  end_square : ∀ b r, equiv ((F.sliceCompletion L s).endMap (b, r)) =
    (L.chartCompletion c u hu).endMap (boundary b, r)
  flow : ∀ x r, equiv ((F.sliceCompletion L s).ambient.completeFlow.flow r x) =
    (L.chartCompletion c u hu).ambient.completeFlow.flow r (equiv x)

/-- The retained inward collar canonically compares the actual joint-family
slice with the separately chosen chart completion. It suffices that their
source parameters agree; no comparison, joint smoothness or marking is input. -/
def chartSliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s u : Parameter)
    (hu : u ∈ c.val.baseSet) (h : F.reparam s = u) : SliceComparison F L s u hu := by
  exact Classical.choice (show Nonempty (SliceComparison F L s u hu) from by
    subst u
    let A := F.sliceNativePresentation L s
    let B := (L.chartNativePresentation c (F.reparam s) hu).localized
    obtain ⟨e, b, hp, hc, hi, hb, he, hf⟩ :=
      A.exists_strictCompletionComparison_of_inwardCollar B
        (F.sliceCompletion L s) (L.chartCompletion c (F.reparam s) hu)
        (F.native.collar s) F.native.width_pos (F.native.embedding s)
        (F.native.zero s) (F.native.ode s)
    exact ⟨⟨e, b, hp, hc, hi, he, hf⟩⟩)

/-- On the original chart neighborhood the comparison targets the original
actual parameter, including either endpoint. -/
def baseSliceComparison (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter) (hs : s ∈ F.base) :
    SliceComparison F L s s (F.base_subset hs) :=
  F.chartSliceComparison L s s (F.base_subset hs) (F.reparam_eq s hs)

end LocalCompletionFamily

namespace OriginalBundleLiouvilleLaws
variable {P : BundlePrimitiveData (k := k) (M := M) E}

/-- Original bundle primitives and Liouville laws produce a joint local
completion family around any actual parameter, including zero and one. -/
def localCompletionFamily (L : OriginalBundleLiouvilleLaws P)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) : LocalCompletionFamily P c t := by
  exact Classical.choice (show Nonempty (LocalCompletionFamily P c t) from by
    obtain ⟨σ, f, U, hf, hσ, hσmem, hU, htU, hUS, hσid⟩ :=
      exists_smooth_interval_cutoff c.val.open_baseSet t ht
    have hα : IsLocallyExtendibleFormFamily (fun s => P.form c (σ s)) :=
      HasSmoothFormFamilyOn.reparam_interval (P.smooth c) σ f hf hσ hσmem
    obtain ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmix,
        hman, hT2, hcount, hInterior, hCylinder, hparameter, hode,
        Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnondeg, hΛflow, hΛfamily⟩ :=
      exists_native_completionFamily_atlas (fun s => P.form c (σ s)) hα
        (fun s => L.nondegenerate c (σ s) (hσmem s))
        (fun s => L.outward c (σ s) (hσmem s))
    exact ⟨⟨σ, f, hf, hσ, hσmem, U, hU, htU, hUS, hσid, hα,
      ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmix, hode,
        Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnondeg, hΛflow, hΛfamily⟩⟩⟩)

end OriginalBundleLiouvilleLaws
end FsFltz.Geometry.IntrinsicSmoothBundle
