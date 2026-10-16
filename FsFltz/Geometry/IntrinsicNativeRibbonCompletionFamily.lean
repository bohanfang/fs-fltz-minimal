import FsFltz.Geometry.IntrinsicCompletionNative
import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas
import FsFltz.Geometry.MovingCompletionComparison
import FsFltz.Geometry.IntrinsicNativeFamilyEndpointComparison
import FsFltz.Geometry.IntrinsicZeroCompletion
import FsFltz.Geometry.IntrinsicZeroRibbonTotalComparison

/-!
# Strict ribbon comparisons on the original completion quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–160;
`def:chain`, lines 163–189; and `sec:lean`, lines 788–814.
An already selected original collar and primitive determine an actual strict
comparison with an independently prescribed completion. Both directions of
the compact inclusion, the whole attached cylinder, the complete flow and
the full intrinsic core are retained. The primitive is not chosen again.

The family applications below keep the same generated pair deformation.
Their comparisons are pointwise in the parameter. Joint comparison of these
exact original ribbon total spaces and its inverse, with real parameter
patch germs at the interval endpoints, is proved in
`IntrinsicNativeRibbonTotalComparisonInverse.lean`. Marking and prescribed
grading transport on the same family remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing
open IntrinsicLiouville

variable {k d : ℕ} [NeZero d] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Compare the exact original quotient and selected primitive with the
prescribed completion. Native Liouville data produce the quotient domain,
its completion and both native boundary identifications. No strict map,
boundary square, flow conjugacy or core correspondence is assumed. -/
theorem exists_strictComparison_of_native_cylinder
    (hdim : k + 1 = d)
    {δ : ℝ} (hδ : 0 < δ)
    (C : ℝ × IntrinsicBoundary.Point k M → M)
    (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
    (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
      (Half δ (IntrinsicBoundary.Point k M)))
    (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
    (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
      ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
          ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
    (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (hode : ∀ b, IsMIntegralCurveOn (fun s => C (s, b))
      (fun x => -liouvilleVector α (exteriorDerivative α) x) (Ico 0 δ))
    (Λ : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hΛsmooth : (completionManifold hδ C hemb hC hboundary hinv hzero).IsSmoothForm Λ)
    (hΛnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      (fun x => (Λ (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x)) = α)
    (hΛcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (cylinder (fun p => C p.val)) Λ = cylinderPrimitive δ α)
    (hΛnd : ∀ x, (completionManifold hδ C hemb hC hboundary hinv hzero).Nondegenerate
      ((completionManifold hδ C hemb hC hboundary hinv hzero).exteriorDerivative Λ) x)
    (D : LiouvilleDomain d) (K : Completion D)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (hp : ∀ x, (D.liouville.primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (e y).val) x) = α x)
    (hc : HasNativeCoordinateExtensions (k := k) D.domain.extension (fun x => (e x).val)) :
    let X := completionManifold hδ C hemb hC hboundary hinv hzero
    let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ∃ (f : X.SmoothEquiv K.ambient.manifold)
      (b : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.domain.boundary)
      (F : CompleteLiouvilleFlow X (X.liouvilleVector Λ)),
      X.pullback K.ambient.manifold f K.ambient.primitive = Λ ∧
      (∀ x, f (original c x) = K.inclusion.map (e x).val) ∧
      (∀ x, f.symm (K.inclusion.map (e x).val) = original c x) ∧
      (∀ x, D.domain.boundaryInclusion.map (b x) = (e x.val).val) ∧
      (∀ p : Band δ (IntrinsicBoundary.Point k M),
        f (cylinder c p) = K.endMap (b p.val.2, -p.val.1)) ∧
      (∀ z s, f (F.flow s z) = K.ambient.completeFlow.flow s (f z)) ∧
      ∀ x, (∀ s : ℝ, 0 ≤ s → F.flow s (original c x) ∈ range (original c)) ↔
        (e x).val ∈ K.core := by
  subst d
  have hnegative (b : IntrinsicBoundary.Point k M) :
      (show Model (k + 1) from chartTangentMap (IntrinsicBoundary.chartAt b).ambient
        b.val (liouvilleVector α (exteriorDerivative α) b.val)) 0 < 0 := by
    obtain ⟨rho, beta, hz, hs, hr, hbeta, hag, hpos⟩ := hout b
    have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source b
      rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
    exact (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt b).mem_atlas hx b.property rho hz hs hr hbeta hag
      (liouvilleVector α (exteriorDerivative α) b.val)).mp hpos
  let L := liouvilleStructure hδ C hemb hC hboundary hinv hzero
    α hnd Λ hΛsmooth hΛnative hΛnd hnegative
  let P := NativeLiouvillePresentation.of_endpoint α
    ⟨compactDomain hδ C hemb hC hboundary hinv hzero, L⟩
    (originalDiffeomorph hδ C hemb hC hboundary hinv hzero)
    (congrFun hΛnative)
    (hasNativeCoordinateExtensions hδ C hemb hC hboundary hinv hzero α hα hnd
      (fun b => by
        rw [normalDefiningFunction_derivative (IntrinsicBoundary.chartAt b).mem_atlas
          (by have h := IntrinsicBoundary.mem_chartAt_source b
              rwa [(IntrinsicBoundary.chartAt b).source_eq] at h)]
        exact neg_pos.mpr (hnegative b)) hode)
  let N := NativeLiouvillePresentation.of_endpoint α D e hp hc
  let K₀ := completion hδ C hemb hC hboundary hinv hzero α hα L hΛnd hΛcylinder
  obtain ⟨f, hf, hs, hi, he⟩ :=
    exists_strictNativeSliceComparison α hα hnd hout P N K₀ K
  have hb (x : IntrinsicBoundary.Point k M) :
      P.nativeBoundaryEquiv x = x := by
    apply P.domain.domain.boundaryInclusion.embedding.injective
    exact (P.nativeBoundaryEquiv_inclusion x).trans
      (compactDomain_boundaryInclusion hδ C hemb hC hboundary hinv hzero x).symm
  have hflow := K₀.ambient.map_flow K.ambient f hf
  have hnative (x : M) : f (original (fun p => C p.val) x) =
      K.inclusion.map (e x).val := hs x
  have hflow' (z : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
      (s : ℝ) : f (K₀.ambient.completeFlow.flow s z) =
      K.ambient.completeFlow.flow s (f z) := hflow z s
  refine ⟨f, N.nativeBoundaryEquiv, K₀.ambient.completeFlow, hf, hs, hi,
    N.nativeBoundaryEquiv_inclusion, ?_, hflow, ?_⟩
  · intro p
    have hrad : -δ < -p.val.1 := neg_lt_neg p.property.1
    have hcyl := boundaryOrbitMap_eq_outwardEndMap hδ C hemb hC hboundary hinv hzero
      α hα L hΛnd hΛcylinder K₀.ambient.completeFlow (p.val.2, -p.val.1) hrad
    rw [outwardEndMap_eq_cylinder hδ C (p.val.2, -p.val.1) hrad] at hcyl
    have hcyl' : K₀.endMap (p.val.2, -p.val.1) = cylinder (fun p => C p.val) p := by
      have hp' : (⟨(-(-p.val.1), p.val.2), neg_lt.mp hrad, mem_univ _⟩ :
          Band δ (IntrinsicBoundary.Point k M)) = p := by
        apply Subtype.ext
        simp only [neg_neg, Prod.mk.eta]
      rw [hp'] at hcyl
      exact hcyl
    exact (congrArg f hcyl').symm.trans
      ((congrArg (fun b => f (K₀.endMap (b, -p.val.1))) (hb p.val.2)).symm.trans
        (he p.val.2 (-p.val.1)))
  · intro x
    change _ ↔ ((e x).val ∈ D.domain.carrier ∧ ∀ s : ℝ, 0 ≤ s →
      K.ambient.completeFlow.flow s (K.inclusion.map (e x).val) ∈
        K.inclusion.map '' D.domain.carrier)
    constructor
    · intro h
      refine ⟨(e x).property, ?_⟩
      intro s hs'
      obtain ⟨y, hy⟩ := h s hs'
      refine ⟨(e y).val, (e y).property, ?_⟩
      exact (hnative y).symm.trans ((congrArg f hy).trans
        ((hflow' _ s).trans (congrArg (K.ambient.completeFlow.flow s) (hnative x))))
    · rintro ⟨_, h⟩ s hs'
      obtain ⟨z, hz, heq⟩ := h s hs'
      obtain ⟨y, hy⟩ := e.surjective ⟨z, hz⟩
      refine ⟨y, f.injective ?_⟩
      have hzy : (e y).val = z := congrArg Subtype.val hy
      exact (hnative y).trans ((congrArg K.inclusion.map hzy).trans
        (heq.trans ((congrArg (K.ambient.completeFlow.flow s) (hnative x).symm).trans
          (hflow' _ s).symm)))

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.PairDeformation
open IntrinsicCompletionGluing IntrinsicLiouville

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original ribbon quotient data and strict slice comparisons with the same
pair deformation. The original total atlas is retained; joint smoothness of
the comparison itself is deliberately not a field of this slice result. -/
structure NativeRibbonCompletionSlices (Q : PairDeformation n)
    (μ : Parameter → Form k M 1)
    (eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
      (Q.pair t).ribbonDomain.domain.Point ∞) where
  width : ℝ
  width_pos : 0 < width
  collar : Parameter → ℝ × IntrinsicBoundary.Point k M → M
  collar_embedding : ∀ t, IsOpenEmbedding
    (fun p : Half width (IntrinsicBoundary.Point k M) => collar t p.val)
  collar_smooth : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
    (𝓡∂ (k + 1)) ∞ (collar t) (Half width (IntrinsicBoundary.Point k M))
  collar_boundary : ∀ t (p : Half width (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (collar t p.val) ↔ p.val.1 = 0
  collar_inverse : ∀ t p, p ∈ Half width (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (collar t p) ∧
        ∀ᶠ q in 𝓝[Half width (IntrinsicBoundary.Point k M)] p, g (collar t q) = q
  collar_zero : ∀ t (b : IntrinsicBoundary.Point k M), collar t (0, b) = b.val
  collar_joint_embedding : IsOpenEmbedding (totalCollar
    (fun t (p : Half width (IntrinsicBoundary.Point k M)) => collar t p.val))
  mixed_germs : HasRealMixedGerms (δ := width) collar
  total_atlas :
    let c := fun t (p : Half width (IntrinsicBoundary.Point k M)) => collar t p.val
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) width
    letI := totalFamilyChartedSpace width_pos collar collar_zero collar_joint_embedding
    IsManifold (familyModel (k + 1)) ∞ (TotalSpace c) ∧
      T2Space (TotalSpace c) ∧ SecondCountableTopology (TotalSpace c) ∧
      ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (totalInterior c) ∧
      ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (totalCylinder c) ∧
      ContMDiff (familyModel (k + 1)) (𝓡∂ 1) ∞ (parameter c)
  collar_ode : ∀ t b, IsMIntegralCurveOn (fun s => collar t (s, b))
    (fun x => -liouvilleVector (μ t) (exteriorDerivative (μ t)) x) (Ico 0 width)
  primitive : ∀ t, (completionManifold width_pos (collar t) (collar_embedding t)
    (collar_smooth t) (collar_boundary t) (collar_inverse t) (collar_zero t)).Form 1
  primitive_smooth : ∀ t, (completionManifold width_pos (collar t) (collar_embedding t)
    (collar_smooth t) (collar_boundary t) (collar_inverse t) (collar_zero t)).IsSmoothForm (primitive t)
  primitive_native : ∀ t,
    letI := completionChartedSpace width_pos (collar t) (collar_embedding t)
      (collar_boundary t) (collar_zero t)
    (fun x => (primitive t (original (fun p => collar t p.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun p => collar t p.val)) x)) = μ t
  primitive_cylinder : ∀ t, (bandManifold width (IntrinsicBoundary.smoothManifold k M)).pullback
    (completionManifold width_pos (collar t) (collar_embedding t) (collar_smooth t)
      (collar_boundary t) (collar_inverse t) (collar_zero t))
    (cylinder (fun p => collar t p.val)) (primitive t) = cylinderPrimitive width (μ t)
  primitive_nondegenerate : ∀ t x,
    (completionManifold width_pos (collar t) (collar_embedding t) (collar_smooth t)
      (collar_boundary t) (collar_inverse t) (collar_zero t)).Nondegenerate
        ((completionManifold width_pos (collar t) (collar_embedding t) (collar_smooth t)
          (collar_boundary t) (collar_inverse t) (collar_zero t)).exteriorDerivative (primitive t)) x
  cylinder_primitive_joint :
    let P := bandManifold width (IntrinsicBoundary.smoothManifold k M)
    P.IsSmoothIntervalFormFamily (fun t => P.pullback
      (completionManifold width_pos (collar t) (collar_embedding t) (collar_smooth t)
        (collar_boundary t) (collar_inverse t) (collar_zero t))
      (cylinder (fun p => collar t p.val)) (primitive t))
  comparison : ∀ t,
    (completionManifold width_pos (collar t) (collar_embedding t) (collar_smooth t)
      (collar_boundary t) (collar_inverse t) (collar_zero t)).SmoothEquiv
        (Q.pair t).ribbonCompletion.ambient.manifold
  boundary_comparison : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair t).ribbonDomain.domain.boundary
  complete_flow : ∀ t,
    let X := completionManifold width_pos (collar t) (collar_embedding t) (collar_smooth t)
      (collar_boundary t) (collar_inverse t) (collar_zero t)
    CompleteLiouvilleFlow X (X.liouvilleVector (primitive t))
  comparison_primitive : ∀ t,
    (completionManifold width_pos (collar t) (collar_embedding t) (collar_smooth t)
      (collar_boundary t) (collar_inverse t) (collar_zero t)).pullback
        (Q.pair t).ribbonCompletion.ambient.manifold (comparison t)
        (Q.pair t).ribbonCompletion.ambient.primitive = primitive t
  comparison_native : ∀ t x, comparison t (original (fun p => collar t p.val) x) =
    (Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val
  inverse_native : ∀ t x, (comparison t).symm
    ((Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val) =
      original (fun p => collar t p.val) x
  boundary_native : ∀ t x, (Q.pair t).ribbonDomain.domain.boundaryInclusion.map
    (boundary_comparison t x) = (eMs t x.val).val
  comparison_cylinder : ∀ t (p : Band width (IntrinsicBoundary.Point k M)),
    comparison t (cylinder (fun p => collar t p.val) p) =
      (Q.pair t).ribbonCompletion.endMap (boundary_comparison t p.val.2, -p.val.1)
  comparison_flow : ∀ t z s, comparison t ((complete_flow t).flow s z) =
    (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s (comparison t z)
  core_equiv : ∀ t x,
    (∀ s : ℝ, 0 ≤ s → (complete_flow t).flow s
      (original (fun p => collar t p.val) x) ∈ range (original (fun p => collar t p.val))) ↔
      (eMs t x).val ∈ (Q.pair t).ribbonCompletion.core
  embedded_core : ∀ t, (Q.pair t).embeddedCore =
    (fun x => (Q.pair t).ribbonEmbedding.map (eMs t x).val) ''
      {x | ∀ s : ℝ, 0 ≤ s → (complete_flow t).flow s
        (original (fun p => collar t p.val) x) ∈ range (original (fun p => collar t p.val))}

/-- The native ribbon family chooses its original collar and primitives once,
then compares those exact quotients with the ribbon completions of the
already selected pair deformation. No new pair or completion is selected. -/
theorem exists_nativeRibbonCompletionFamily_slice_comparisons (Q : PairDeformation n)
    (hdim : k + 1 = 2 * n - 2)
    (μ : Parameter → Form k M 1) (hμ : IsLocallyExtendibleFormFamily μ)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (μ t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (μ t) (exteriorDerivative (μ t)) x.val)))
    (eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
      (Q.pair t).ribbonDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ribbonDomain.liouville.primitive (eMs t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMs t y).val) x) = μ t x)
    (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ribbonDomain.domain.extension (fun x => (eMs t x).val)) :
    Nonempty (NativeRibbonCompletionSlices Q μ eMs) := by
  obtain ⟨δ, hδ, C, hemb, hC, hb, hi, hz, hj, hmixed,
      hman, hT2, hcount, hI, hCyl, hparam, hode, Λ, hΛ, hn, hcyl, hndΛ, _, hfamily⟩ :=
    exists_native_completionFamily_atlas μ hμ hnd hout
  have hslice (t : Parameter) := exists_strictComparison_of_native_cylinder hdim hδ (C t)
    (hemb t) (hC t) (hb t) (hi t) (hz t) (μ t) (hμ.slice t) (hnd t) (hout t)
    (hode t) (Λ t) (hΛ t) (hn t) (hcyl t) (hndΛ t)
    (Q.pair t).ribbonDomain (Q.pair t).ribbonCompletion (eMs t) (hp t) (hc t)
  choose f b F hf hnative hinverse hboundary hcylinder hflow hcore using hslice
  refine ⟨{
    width := δ, width_pos := hδ, collar := C, collar_embedding := hemb
    collar_smooth := hC, collar_boundary := hb, collar_inverse := hi, collar_zero := hz
    collar_joint_embedding := hj, mixed_germs := hmixed
    total_atlas := ⟨hman, hT2, hcount, hI, hCyl, hparam⟩, collar_ode := hode
    primitive := Λ, primitive_smooth := hΛ, primitive_native := hn
    primitive_cylinder := hcyl, primitive_nondegenerate := hndΛ
    cylinder_primitive_joint := hfamily, comparison := f, boundary_comparison := b
    complete_flow := F, comparison_primitive := hf, comparison_native := hnative
    inverse_native := hinverse, boundary_native := hboundary
    comparison_cylinder := hcylinder, comparison_flow := hflow, core_equiv := hcore
    embedded_core := ?_ }⟩
  intro t
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := (eMs t).surjective ⟨x, hx.1⟩
    have hy' : (eMs t y).val = x := congrArg Subtype.val hy
    exact ⟨y, (hcore t y).mpr (hy' ▸ hx), congrArg (Q.pair t).ribbonEmbedding.map hy'⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(eMs t x).val, (hcore t x).mp hx, rfl⟩

end FsFltz.Geometry.PairDeformation

namespace FsFltz.Geometry.PairDeformation
open IntrinsicZeroLiouville

variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- The zero-dimensional ribbon's completion is the literal original native
manifold. Its comparison is the canonical inclusion diffeomorphism of the
same selected endpoint completion. -/
structure NativeZeroRibbonCompletionSlices (Q : PairDeformation 1)
    (μ : Parameter → (sourceManifold M).Form 1)
    (eFs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
        (Q.pair t).ribbonDomain.domain.Point ∞) where
  comparison : ∀ t, (sourceManifold M).SmoothEquiv (Q.pair t).ribbonCompletion.ambient.manifold
  comparison_canonical : ∀ t, comparison t = endpointCompletionDiffeomorph
    (Q.pair t).ribbonDomain (Q.pair t).ribbonCompletion (eFs t)
  comparison_primitive : ∀ t, (sourceManifold M).pullback
    (Q.pair t).ribbonCompletion.ambient.manifold (comparison t)
      (Q.pair t).ribbonCompletion.ambient.primitive = μ t
  comparison_native : ∀ t x, comparison t x =
    (Q.pair t).ribbonCompletion.inclusion.map (eFs t x).val
  inverse_native : ∀ t x, (comparison t).symm
    ((Q.pair t).ribbonCompletion.inclusion.map (eFs t x).val) = x
  comparison_flow : ∀ t x s,
    comparison t ((sourceCompletion (μ t)).ambient.completeFlow.flow s x) =
      (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s (comparison t x)
  core_equiv : ∀ t x, x ∈ (sourceCompletion (μ t)).core ↔
    (eFs t x).val ∈ (Q.pair t).ribbonCompletion.core
  embedded_core : ∀ t, (Q.pair t).embeddedCore =
    (fun x => (Q.pair t).ribbonEmbedding.map (eFs t x).val) '' (sourceCompletion (μ t)).core

/-- Canonical strict comparisons from the literal native zero ribbon
completion to the ribbon completion of the same selected pair. -/
theorem exists_nativeZeroRibbonCompletionFamily_slice_comparisons (Q : PairDeformation 1)
    (μ : Parameter → (sourceManifold M).Form 1)
    (eFs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
        (Q.pair t).ribbonDomain.domain.Point ∞) :
    Nonempty (NativeZeroRibbonCompletionSlices Q μ eFs) := by
  let S := fun t => endpointCompletionDiffeomorph
    (Q.pair t).ribbonDomain (Q.pair t).ribbonCompletion (eFs t)
  have hp (t : Parameter) : (sourceManifold M).pullback
      (Q.pair t).ribbonCompletion.ambient.manifold (S t)
        (Q.pair t).ribbonCompletion.ambient.primitive = μ t :=
    ((sourceManifold M).oneForm_eq_zero_of_dimension_zero _).trans
      ((sourceManifold M).oneForm_eq_zero_of_dimension_zero _).symm
  have hn (t : Parameter) (x : M) : S t x =
      (Q.pair t).ribbonCompletion.inclusion.map (eFs t x).val := rfl
  have hc (t : Parameter) (x : M) : x ∈ (sourceCompletion (μ t)).core ↔
      (eFs t x).val ∈ (Q.pair t).ribbonCompletion.core := by
    rw [sourceCompletion_core, Completion.core_eq_carrier_of_dimension_zero]
    exact iff_of_true (mem_univ _) (eFs t x).property
  refine ⟨{
    comparison := S, comparison_canonical := fun _ => rfl
    comparison_primitive := hp, comparison_native := hn
    inverse_native := fun t x => (congrArg (S t).symm (hn t x)).symm.trans
      ((S t).symm_apply_apply x)
    comparison_flow := ?_, core_equiv := hc, embedded_core := ?_ }⟩
  · intro t x s
    exact (sourceCompletion (μ t)).ambient.map_flow
      (Q.pair t).ribbonCompletion.ambient (S t) (hp t) x s
  · intro t
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy⟩ := (eFs t).surjective ⟨x, hx.1⟩
      have hy' : (eFs t y).val = x := congrArg Subtype.val hy
      exact ⟨y, (hc t y).mpr (hy' ▸ hx), congrArg (Q.pair t).ribbonEmbedding.map hy'⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(eFs t x).val, (hc t x).mp hx, rfl⟩

/-- The all-real comparison of the same native zero ribbon family agrees
with the retained canonical strict slice comparisons in both directions. -/
theorem NativeZeroRibbonCompletionSlices.exists_totalComparison
    {Q : PairDeformation 1} {μ : Parameter → (sourceManifold M).Form 1}
    {eFs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
        (Q.pair t).ribbonDomain.domain.Point ∞}
    (S : NativeZeroRibbonCompletionSlices Q μ eFs)
    (RM : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞)
    (hRM : IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) RM)
    (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
      (eFs parameterZero (RM t.val x)).val = (eFs t x).val) :
    ∃ F : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
        (ℝ × M) (ℝ × Q.source.ribbonCompletion.ambient.manifold.Point) ∞,
      (∀ z, (F z).1 = z.1) ∧ (∀ z, (F.symm z).1 = z.1) ∧
      (∀ (t : Parameter) x, F (t.val, x) =
        (t.val, (Q.ribbonCompletionPresentation t).equiv.symm (S.comparison t x))) ∧
      (∀ (t : Parameter) y, F.symm (t.val, y) =
        (t.val, (S.comparison t).symm ((Q.ribbonCompletionPresentation t).equiv y))) := by
  obtain ⟨F, hp, hip, hf, hi⟩ := Q.exists_nativeZeroRibbonTotalComparison eFs RM hRM hsquare
  refine ⟨F, hp, hip, ?_, ?_⟩
  · intro t x
    rw [S.comparison_canonical]
    exact hf t x
  · intro t y
    rw [S.comparison_canonical]
    exact hi t y

end FsFltz.Geometry.PairDeformation
