import FsFltz.Geometry.IntervalComplexFamilyExtension
import FsFltz.Geometry.MaslovTransport

/-!
# Native interval sections on the specified graded deformation

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 225–232;
`g:chain`, lines 407–413; and `sec:lean`, lines 794–814.

The interval-bundle bridge applies to the actual completed family of a
graded pair deformation. Its section recovers the prescribed endpoint tensors
through that deformation's own completion presentations. Conversely, genuine
local scalar C∞ extension witnesses for an arbitrary interval section produce
the encoded grading on this very deformation. The source's endpoint extension
convention is explicit; bare native `ContMDiff ∞` is not treated as an extension
theorem. No geometric deformation or prescribed endpoint grading is invented.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Bundle

namespace FsFltz.Geometry.GradedPairDeformation

/-- Source-local extensions of both the complex endomorphism and the
section's scalar coordinates reconstruct a grading on this very completed
deformation. All original interval values and both marked endpoint
representatives are retained. A global smooth complex-field extension is
produced, rather than supplied as a hypothesis. -/
theorem exists_of_localExtensions {n : ℕ} {D : PairDeformation n}
    {source : D.source.Maslov} {target : D.target.Maslov}
    (eta : ℝ → D.source.ambientManifold.Form 2)
    (heta : ∀ t : Parameter, eta t.val =
      D.source.ambientManifold.exteriorDerivative (D.completedPrimitive t))
    (J : ℝ → AlmostComplexField D.source.ambientManifold)
    (hcompatible : ∀ t ∈ parameterInterval,
      IsCompatibleAlmostComplex D.source.ambientManifold (eta t) (J t))
    (hJ : HasLocalSmoothIntervalComplexExtensions D.source.ambientManifold J)
    (s : (p : Parameter × D.source.ambientManifold.Point) →
      CanonicalTensorSquare (J p.1.val p.2))
    (hnz : ∀ p, s p ≠ 0)
    (hs : HasLocalSmoothIntervalTensorCoefficients D.source.ambientManifold J s)
    (hJ₀ : J 0 = pullbackAlmostComplex D.source.ambientManifold
      D.source.ambientManifold (D.ambientCompletionPresentation parameterZero).equiv source.J)
    (hJ₁ : J 1 = pullbackAlmostComplex D.source.ambientManifold
      D.target.ambientManifold (D.ambientCompletionPresentation parameterOne).equiv target.J)
    (hs₀ : ∀ x, (canonicalSquareMap (J 0 x) (s (parameterZero, x))).val =
      pullbackSquaredTensor D.source.ambientManifold D.source.ambientManifold
        (D.ambientCompletionPresentation parameterZero).equiv source.tensor x)
    (hs₁ : ∀ x, (canonicalSquareMap (J 1 x) (s (parameterOne, x))).val =
      pullbackSquaredTensor D.source.ambientManifold D.target.ambientManifold
        (D.ambientCompletionPresentation parameterOne).equiv target.tensor x) :
    ∃ g : GradedPairDeformation D source target,
      (∀ t : Parameter, g.family.J t.val = J t.val) ∧
      ∀ p : Parameter × D.source.ambientManifold.Point,
        g.family.tensor p.1.val p.2 = (canonicalSquareMap (J p.1.val p.2) (s p)).val := by
  obtain ⟨f, hfJ, hf⟩ := exists_maslovFamily_of_localExtensions J hcompatible hJ s hnz hs
  let g : GradedPairDeformation D source target :=
    { etaExtension := eta
      eta_agrees := heta
      family := f
      sourceJ := (hfJ parameterZero).trans hJ₀
      targetJ := (hfJ parameterOne).trans hJ₁
      sourceTensor := funext (fun x => (hf (parameterZero, x)).trans (hs₀ x))
      targetTensor := funext (fun x => (hf (parameterOne, x)).trans (hs₁ x)) }
  exact ⟨g, hfJ, hf⟩

/-- Genuine scalar extension data reconstruct a grading on the same
completed geometric deformation, preserving every interval tensor and
the endpoint values in that deformation's specified presentations. -/
theorem exists_of_localScalarExtensions {n : ℕ} {D : PairDeformation n}
    {source : D.source.Maslov} {target : D.target.Maslov}
    (eta : ℝ → D.source.ambientManifold.Form 2)
    (heta : ∀ t : Parameter, eta t.val =
      D.source.ambientManifold.exteriorDerivative (D.completedPrimitive t))
    (J : ℝ → AlmostComplexField D.source.ambientManifold)
    (hcompatible : ∀ t ∈ parameterInterval,
      IsCompatibleAlmostComplex D.source.ambientManifold (eta t) (J t))
    (hJ : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => almostComplexInChart D.source.ambientManifold a (J z.1) z.2))
    (s : (p : Parameter × D.source.ambientManifold.Point) →
      CanonicalTensorSquare (J p.1.val p.2))
    (hnz : ∀ p, s p ≠ 0)
    (hs : HasLocalSmoothIntervalTensorCoefficients D.source.ambientManifold J s)
    (hJ₀ : J 0 = pullbackAlmostComplex D.source.ambientManifold
      D.source.ambientManifold (D.ambientCompletionPresentation parameterZero).equiv source.J)
    (hJ₁ : J 1 = pullbackAlmostComplex D.source.ambientManifold
      D.target.ambientManifold (D.ambientCompletionPresentation parameterOne).equiv target.J)
    (hs₀ : ∀ x, (canonicalSquareMap (J 0 x) (s (parameterZero, x))).val =
      pullbackSquaredTensor D.source.ambientManifold D.source.ambientManifold
        (D.ambientCompletionPresentation parameterZero).equiv source.tensor x)
    (hs₁ : ∀ x, (canonicalSquareMap (J 1 x) (s (parameterOne, x))).val =
      pullbackSquaredTensor D.source.ambientManifold D.target.ambientManifold
        (D.ambientCompletionPresentation parameterOne).equiv target.tensor x) :
    ∃ g : GradedPairDeformation D source target, g.family.J = J ∧
      ∀ p : Parameter × D.source.ambientManifold.Point,
        g.family.tensor p.1.val p.2 = (canonicalSquareMap (J p.1.val p.2) (s p)).val := by
  obtain ⟨f, hfJ, hf⟩ := exists_maslovFamily_of_localScalarExtensions hcompatible hJ s hnz hs
  let g : GradedPairDeformation D source target :=
    { etaExtension := eta
      eta_agrees := heta
      family := f
      sourceJ := by rw [hfJ]; exact hJ₀
      targetJ := by rw [hfJ]; exact hJ₁
      sourceTensor := funext (fun x => (hf (parameterZero, x)).trans (hs₀ x))
      targetTensor := funext (fun x => (hf (parameterOne, x)).trans (hs₁ x)) }
  exact ⟨g, hfJ, hf⟩

set_option maxHeartbeats 400000 in
/-- A grading on the specified completed deformation gives a native smooth
nonzero section, with the original interval values and marked endpoints. -/
theorem exists_native_intervalTensorSection {n : ℕ} {D : PairDeformation n}
    {source : D.source.Maslov} {target : D.target.Maslov}
    (g : GradedPairDeformation D source target) :
    let a := intervalCanonicalTensorSquareVectorPrebundle g.family
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    let I := (𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))
    ∃ s : (p : Parameter × D.source.ambientManifold.Point) →
        CanonicalTensorSquare (g.family.J p.1.val p.2),
      ContMDiff I (I.prod 𝓘(ℝ, ℂ)) ∞
        (fun p => (⟨p, s p⟩ : TotalSpace ℂ
          (fun p : Parameter × D.source.ambientManifold.Point =>
            CanonicalTensorSquare (g.family.J p.1.val p.2)))) ∧
      (∀ p, s p ≠ 0) ∧
      (∀ p, (canonicalSquareMap (g.family.J p.1.val p.2) (s p)).val =
        g.family.tensor p.1.val p.2) ∧
      (∀ x, (canonicalSquareMap (g.family.J 0 x) (s (parameterZero, x))).val =
        pullbackSquaredTensor D.source.ambientManifold D.source.ambientManifold
          (D.ambientCompletionPresentation parameterZero).equiv source.tensor x) ∧
      (∀ x, (canonicalSquareMap (g.family.J 1 x) (s (parameterOne, x))).val =
        pullbackSquaredTensor D.source.ambientManifold D.target.ambientManifold
          (D.ambientCompletionPresentation parameterOne).equiv target.tensor x) := by
  dsimp only
  have hmap := fun p => congrArg Subtype.val (g.family.canonicalSquareMap_intervalTensorSection p)
  refine ⟨g.family.intervalTensorSection, g.family.contMDiff_intervalTensorSection,
    g.family.intervalTensorSection_ne_zero, hmap, ?_, ?_⟩
  · intro x
    exact (hmap (parameterZero, x)).trans (congrFun g.sourceTensor x)
  · intro x
    exact (hmap (parameterOne, x)).trans (congrFun g.targetTensor x)

end FsFltz.Geometry.GradedPairDeformation
