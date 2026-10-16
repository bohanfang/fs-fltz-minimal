import FsFltz.Geometry.NativeCanonicalSectionGraphExtension
import FsFltz.Geometry.IntrinsicNativeCompletionGradingSectionGerms

/-!
# Original grading graph extensions produce native section germs

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:maslov`, lines 212–232; `g:chain`, lines 407–413; and `sec:lean`,
lines 794–814. Original interior and cylindrical-end tensor values are
represented by smooth maps into the independently constructed native bundle.
The maps need preserve their base only on the original parameter locus.
Rectification constructs actual extending sections and proves the full
original matching equations, retaining all chart derivatives and slots.

The original varying completed-family bundle atlas and the correspondence
between source smoothness and these local graph extensions remain pending.
No scalar or tensor smoothness is supplied, and no extending section is an
input. This is a conditional source graph reconstruction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A native graph-map extension need not be a section outside the source
locus. Its smoothness is actual bundle `ContMDiff`, with no scalar or full
tensor regularity field. -/
structure NativeCoordinateCanonicalGraphGerm (P : Model (2 * n) ≃L[ℝ] F)
    (A : Set E) (p : E) where
  complexGerm : NativeCoordinateComplexGerm P A p
  domain : TopologicalSpace.Opens E
  subset_bundlePatch : (domain : Set E) ⊆ complexGerm.bundlePatch.domain
  mem_domain : p ∈ domain
  bundleMap : domain → TotalSpace ℂ (fun z : domain => CanonicalTensorSquare
    ((complexGerm.bundlePatch.restrict domain subset_bundlePatch).complex z))
  smooth_bundleMap : (complexGerm.bundlePatch.restrict domain subset_bundlePatch).IsSmoothBundleMap bundleMap
  projection_locus : ∀ z : domain, z.val ∈ A → (bundleMap z).proj = z
  nonzero_center : (bundleMap ⟨p, mem_domain⟩).snd ≠ 0

namespace NativeCoordinateCanonicalGraphGerm

variable {P : Model (2 * n) ≃L[ℝ] F} {A : Set E} {p : E}
  (g : NativeCoordinateCanonicalGraphGerm P A p)

def patch : NativeCoordinateCanonicalPatch P g.complexGerm.field A :=
  g.complexGerm.bundlePatch.restrict g.domain g.subset_bundlePatch

/-- An actual extending section is produced, rather than supplied.
The smaller source graph domain and every original tensor value are kept. -/
theorem exists_sectionGerm :
    ∃ h : NativeCoordinateCanonicalSectionGerm P A p,
      h.complexGerm = g.complexGerm ∧ (∀ z : h.domain, h.tensorSection z ≠ 0) ∧
      ∃ hsub : (h.domain : Set E) ⊆ g.domain,
        ∀ (z : h.domain), z.val ∈ A →
          (canonicalSquareMap (h.patch.complex z) (h.tensorSection z)).val =
            (canonicalSquareMap (g.patch.complex (g.bundleMap ⟨z.val, hsub z.property⟩).proj)
              (g.bundleMap ⟨z.val, hsub z.property⟩).snd).val :=
  g.complexGerm.exists_sectionGerm_of_graphExtension g.domain g.subset_bundlePatch
    g.mem_domain g.bundleMap g.smooth_bundleMap g.projection_locus g.nonzero_center

end NativeCoordinateCanonicalGraphGerm

namespace PairDeformation
open IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t x, C t (0, x) = x.val)
  (Jnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (Tnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)

local instance nativeGraphGermBandCharts :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance nativeGraphGermProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance nativeGraphGermProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

/-- Original interior graph-map extensions. Off the original parameter
locus their base projection may drift, so extending sections are conclusions. -/
def HasNativeInteriorGradingGraphExtensions
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1)) : Prop :=
  ∀ (t : Parameter) (u : IntrinsicInterior.Point k M),
    ∃ g : NativeCoordinateCanonicalGraphGerm P
      (parameterInterval ×ˢ (univ : Set (Model (k + 1))))
      (t.val, chartAt (Model (k + 1)) u u),
      ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
        w ∈ (chartAt (Model (k + 1)) u).source →
        ∀ hw : (s.val, chartAt (Model (k + 1)) u w) ∈ g.domain,
          letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
          let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
          let H := (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
            (chartAt (Model (k + 1)) u) w).comp
            (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j w).inverse
          g.complexGerm.field (s.val, chartAt (Model (k + 1)) u w) =
            H.comp ((Jnative s (j w)).comp H.inverse) ∧
          (canonicalSquareMap (g.patch.complex (g.bundleMap ⟨_, hw⟩).proj)
            (g.bundleMap ⟨_, hw⟩).snd).val =
            ((Tnative s (j w)).compContinuousLinearMap (fun _ => H.inverse)).compContinuousLinearMap
              (fun _ => P.toContinuousLinearMap)

/-- The corresponding original boundary–radial graph extensions,
including radius zero and both parameter endpoints. -/
def HasNativeEndGradingGraphExtensions
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ)) : Prop :=
  ∀ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
    ∃ g : NativeCoordinateCanonicalGraphGerm P
      (parameterInterval ×ˢ (univ : Set (Model k × ℝ)))
      (t.val, chartAt (Model k × ℝ) (x, r) (x, r)),
      ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
        letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
        let w := endBandCoordinates p
        w ∈ (chartAt (Model k × ℝ) (x, r)).source →
        ∀ hw : (s.val, chartAt (Model k × ℝ) (x, r) w) ∈ g.domain,
          let j := cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
          let H := (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
            (chartAt (Model k × ℝ) (x, r)) w).comp
            ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
              (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse)
          g.complexGerm.field (s.val, chartAt (Model k × ℝ) (x, r) w) =
            H.comp ((Jnative s (j p)).comp H.inverse) ∧
          (canonicalSquareMap (g.patch.complex (g.bundleMap ⟨_, hw⟩).proj)
            (g.bundleMap ⟨_, hw⟩).snd).val =
            ((Tnative s (j p)).compContinuousLinearMap (fun _ => H.inverse)).compContinuousLinearMap
              (fun _ => P.toContinuousLinearMap)

omit [T2Space M] [SecondCountableTopology M] in
/-- Rectifying native graph maps supplies the actual extending interior
bundle sections with every original full tensor value retained. -/
theorem nativeInteriorGradingSectionGerms_of_graphExtensions
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (hg : HasNativeInteriorGradingGraphExtensions hδ C hemb hboundary hzero Jnative Tnative P) :
    HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero Jnative Tnative P := by
  intro t u
  obtain ⟨g, hm⟩ := hg t u
  obtain ⟨h, heJ, _, hsub, heT⟩ := g.exists_sectionGerm
  refine ⟨h, ?_⟩
  intro s w hw hwh
  obtain ⟨hJ, hT⟩ := hm s w hw (hsub hwh)
  refine ⟨?_, ?_⟩
  · rw [heJ]
    exact hJ
  · exact (heT ⟨_, hwh⟩ ⟨s.property, mem_univ _⟩).trans hT

omit [T2Space M] [SecondCountableTopology M] in
/-- End graph rectification retains the actual cylinder derivative and
radial convention, and supplies the previously assumed extending sections. -/
theorem nativeEndGradingSectionGerms_of_graphExtensions
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (hg : HasNativeEndGradingGraphExtensions hδ C hemb hboundary hzero Jnative Tnative P) :
    HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero Jnative Tnative P := by
  intro t x r hr
  obtain ⟨g, hm⟩ := hg t x r hr
  obtain ⟨h, heJ, _, hsub, heT⟩ := g.exists_sectionGerm
  refine ⟨h, ?_⟩
  intro s p
  dsimp only
  intro hw hwh
  obtain ⟨hJ, hT⟩ := hm s p hw (hsub hwh)
  refine ⟨?_, ?_⟩
  · rw [heJ]
    exact hJ
  · exact (heT ⟨_, hwh⟩ ⟨s.property, mem_univ _⟩).trans hT

end PairDeformation
end FsFltz.Geometry
