import FsFltz.Geometry.CoordinateCoframePullback

/-!
# Smooth coframe and scalar pullback in native coordinates

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The same genuine spatial derivative pulls back
the coframe and its complete scalar multiple of the canonical square.
The coordinate target may have an arbitrary real normed model space.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

/-- Smooth source coframes and scalar coefficients pull back through a
jointly smooth coordinate map whose spatial derivatives are invertible.
All regularity holds on a real-open neighborhood, including parameter
endpoints. The scalar is allowed to vanish. -/
theorem exists_coordinateCoframeScalar_pullback {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : SmoothManifold (2 * n)) (φ : ℝ × N.Point → F)
    {R : Set (ℝ × N.Point)} (hR : IsOpen R)
    (hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, F) ∞ φ R)
    (hi : ∀ z ∈ R,
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, F)
        (fun x => φ (z.1, x)) z.2).IsInvertible)
    (p : ℝ × N.Point) (hp : p ∈ R)
    {W : Set (ℝ × F)} (hW : IsOpen W) (hpW : (p.1, φ p) ∈ W)
    (C : (ℝ × F) → F →L[ℝ] TangentCoordinates n)
    (hC : ContDiffOn ℝ ∞ C W) (hCi : ∀ q ∈ W, (C q).IsInvertible)
    (a : (ℝ × F) → ℂ) (ha : ContDiffOn ℝ ∞ a W) :
    ∃ U : Set (ℝ × N.Point),
      IsOpen U ∧ p ∈ U ∧
      U ⊆ R ∩ (fun z : ℝ × N.Point => (z.1, φ z)) ⁻¹' W ∧
      IsSmoothVerticalCoframeOn N (pullbackCoordinateVerticalCoframe N φ C) U ∧
      (∀ z ∈ U, (pullbackCoordinateVerticalCoframe N φ C z).IsInvertible) ∧
      IsSmoothVerticalEndomorphismOn N
        (fun z => coframeComplexStructure (pullbackCoordinateVerticalCoframe N φ C z)) U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞
        (fun z => a (z.1, φ z)) U ∧
      IsSmoothVerticalSquaredTensorOn N
        (fun z => a (z.1, φ z) •
          coframeSquaredGenerator (pullbackCoordinateVerticalCoframe N φ C z)) U := by
  let q := fun z : ℝ × N.Point => (z.1, φ z)
  have hq : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ q R := contMDiffOn_fst.prodMk hφ
  let U := R ∩ q ⁻¹' W
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hR hW
  have hB : IsSmoothVerticalCoframeOn N (pullbackCoordinateVerticalCoframe N φ C) U :=
    isSmoothVerticalCoframeOn_coordinatePullback N φ hR hφ hW C hC
  have hBi : ∀ z ∈ U, (pullbackCoordinateVerticalCoframe N φ C z).IsInvertible := by
    intro z hz
    exact (hCi _ hz.2).comp (hi z hz.1)
  have ha' : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℂ) ∞ (fun z => a (z.1, φ z)) U := by
    have haM : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℂ) ∞ a W := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact ha.contMDiffOn
    exact haM.comp (hq.mono inter_subset_left) inter_subset_right
  exact ⟨U, hU, ⟨hp, hpW⟩, Subset.refl _, hB, hBi,
    hB.complexEndomorphism hBi, ha', hB.squaredGenerator.smul hU ha'⟩

end FsFltz.Geometry
