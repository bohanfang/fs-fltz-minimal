import FsFltz.Geometry.NativeCoordinateCanonicalSection
import FsFltz.Geometry.IntrinsicNativeCompletionGradingDescent

/-!
# Original native bundle section germs produce both grading branches

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232;
`g:chain`, lines 407–413; and `sec:lean`, lines 794–814.
The inputs are actual extending native canonical-square sections on local
real open source patches. Their complex bundle is produced from the source
endomorphism germ. Native bundle smoothness, natural square multiplication,
and nonvanishing at the center derive full source tensor extensions and laws.

These local extending bundle sections are explicit inputs. This module does
not assert their existence from arbitrary interval-only bundle smoothness.
All matching equations concern the original interior/cylinder inclusions,
with the original source chart and every tangent slot retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology

namespace FsFltz.Geometry.PairDeformation
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

local instance nativeSectionGermBandCharts :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance nativeSectionGermProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance nativeSectionGermProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

/-- Source-local native bundle extension data on the original interior
patches. No full tensor extension or its smoothness is supplied. -/
def HasNativeInteriorGradingSectionGerms
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1)) : Prop :=
  ∀ (t : Parameter) (u : IntrinsicInterior.Point k M),
    ∃ g : NativeCoordinateCanonicalSectionGerm P
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
          (canonicalSquareMap (g.patch.complex ⟨_, hw⟩) (g.tensorSection ⟨_, hw⟩)).val =
            ((Tnative s (j w)).compContinuousLinearMap (fun _ => H.inverse)).compContinuousLinearMap
              (fun _ => P.toContinuousLinearMap)

/-- The corresponding actual bundle section extensions on the original
boundary–radial end patches, including radius zero. -/
def HasNativeEndGradingSectionGerms
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ)) : Prop :=
  ∀ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
    ∃ g : NativeCoordinateCanonicalSectionGerm P
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
          (canonicalSquareMap (g.patch.complex ⟨_, hw⟩) (g.tensorSection ⟨_, hw⟩)).val =
            ((Tnative s (j p)).compContinuousLinearMap (fun _ => H.inverse)).compContinuousLinearMap
              (fun _ => P.toContinuousLinearMap)

omit [T2Space M] [SecondCountableTopology M] in
/-- An actual native extending interior bundle section produces all full
tensor coordinate regularity, canonicality and nonvanishing inputs. -/
theorem nativeInteriorGradingCoordinateExtensions_of_sectionGerms
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (hg : HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero Jnative Tnative P) :
    HasNativeInteriorGradingCoordinateExtensions hδ C hemb hboundary hzero Jnative Tnative P := by
  intro t u
  obtain ⟨g, hm⟩ := hg t u
  refine ⟨g.domain, g.domain.isOpen, g.mem_domain,
    g.complexGerm.field, g.smooth_field, ?_, g.tensor, g.smooth_tensor, ?_,
    g.tensor_nonzero_center, ?_⟩
  · intro s w hw
    exact g.complexGerm.square (s.val, w)
      ⟨(g.subset_bundlePatch.trans g.complexGerm.bundlePatch_subset) hw,
        s.property, mem_univ _⟩
  · intro s w hw
    exact g.tensor_canonical hw ⟨s.property, mem_univ _⟩
  · intro s w hw hwg
    obtain ⟨hJ, hT⟩ := hm s w hw hwg
    refine ⟨hJ, ?_⟩
    exact g.patch.tensorExtension_eq_of_normalized g.tensorSection hwg _ hT

omit [T2Space M] [SecondCountableTopology M] in
/-- The same native bundle reconstruction supplies the original end
coordinate predicate, retaining its cylinder derivative and radial sign. -/
theorem nativeEndGradingCoordinateExtensions_of_sectionGerms
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (hg : HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero Jnative Tnative P) :
    HasNativeEndGradingCoordinateExtensions hδ C hemb hboundary hzero Jnative Tnative P := by
  intro t x r hr
  obtain ⟨g, hm⟩ := hg t x r hr
  refine ⟨g.domain, g.domain.isOpen, g.mem_domain,
    g.complexGerm.field, g.smooth_field, ?_, g.tensor, g.smooth_tensor, ?_,
    g.tensor_nonzero_center, ?_⟩
  · intro s w hw
    exact g.complexGerm.square (s.val, w)
      ⟨(g.subset_bundlePatch.trans g.complexGerm.bundlePatch_subset) hw,
        s.property, mem_univ _⟩
  · intro s w hw
    exact g.tensor_canonical hw ⟨s.property, mem_univ _⟩
  · intro s p
    dsimp only
    intro hw hwg
    obtain ⟨hJ, hT⟩ := hm s p hw hwg
    refine ⟨hJ, ?_⟩
    exact g.patch.tensorExtension_eq_of_normalized g.tensorSection hwg _ hT

end FsFltz.Geometry.PairDeformation
