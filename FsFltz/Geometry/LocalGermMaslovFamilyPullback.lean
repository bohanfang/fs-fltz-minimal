import FsFltz.Geometry.IntervalMaslovFamilyPullback
import FsFltz.Geometry.IntrinsicBundleNativeData

/-!
# Maslov pullback from real smooth map germs

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 225–232,
and `sec:lean`, lines 788–814.
The specified interval diffeomorphisms need only actual per-point real-open
forward germs. Each local coframe construction uses its own germ. Spatial
differential inversion gives complex-field regularity, and the same coframe
pulls back the actual tensor section. The resulting conditional grading is
on the original specified pair deformation and retains its endpoint equations.
Descent of an independently preselected original-atlas section still requires
overlap covariance; it is not supplied by this adapter.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct Classical
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicSmoothBundle

namespace FsFltz.Geometry

/-- A coframe pullback only needs a real smooth map near the point under
consideration. No single real neighborhood covers the whole interval family. -/
theorem exists_intervalCanonicalChart_pullback_at {n : ℕ}
    (M N : SmoothManifold (2 * n)) (e : Parameter → M.SmoothEquiv N)
    (f : ℝ → M.Point → N.Point)
    {R : Set (ℝ × M.Point)} (hR : IsOpen R)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × M.Point => f p.1 p.2) R)
    (hfeq : ∀ t : Parameter, f t.val = e t)
    {J : ℝ → AlmostComplexField N} (c : IntervalCanonicalChart N J)
    {V : Set (ℝ × N.Point)} (hV : IsOpen V) (hVc : V ⊆ c.domain)
    (p : Parameter × M.Point) (hRp : intervalParameterInclusion M p ∈ R)
    (hp : (p.1.val, e p.1 p.2) ∈ V) :
    ∃ c' : IntervalCanonicalChart M (intervalPullbackAlmostComplex M N e J),
      intervalParameterInclusion M p ∈ c'.domain ∧
      c'.domain ⊆ R ∩ (fun q : ℝ × M.Point => (q.1, f q.1 q.2)) ⁻¹' V ∧
      c'.coframe = pullbackVerticalCoframe M N f c.coframe := by
  let F := fun q : ℝ × M.Point => (q.1, f q.1 q.2)
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ F R := contMDiffOn_fst.prodMk hf
  let S := R ∩ F ⁻¹' V
  have hS : IsOpen S := hF.continuousOn.isOpen_inter_preimage hR hV
  have hpS : intervalParameterInclusion M p ∈ S := by
    refine ⟨hRp, ?_⟩
    change (p.1.val, f p.1.val p.2) ∈ V
    rwa [hfeq p.1]
  let C := pullbackVerticalCoframe M N f c.coframe
  have hC : IsSmoothVerticalCoframeOn M C S := by
    intro b
    exact (isSmoothVerticalCoframeOn_pullback M N f hR hf c.isOpen_domain
      c.coframe c.smooth_coframe b).mono (fun q hq => ⟨hq.1, hq.2.1, hVc hq.2.2⟩)
  let a := p.2
  let d := chartAt (Model (2 * n)) a
  let D := intrinsicParameterCoordinateDomain M a S
  have hD : IsOpen D := isOpen_intrinsicParameterCoordinateDomain M a hS
  let A : (ℝ × Model (2 * n)) → Model (2 * n) →L[ℝ] TangentCoordinates n := fun q =>
    (C (q.1, d.symm q.2)).comp (M.inverseChartTangentMap a q.2)
  let W := D ∩ A ⁻¹' {L | L.IsInvertible}
  have hW : IsOpen W := (hC a).continuousOn.isOpen_inter_preimage hD
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpD : (p.1.val, d p.2) ∈ D := by
    refine ⟨⟨mem_univ _, d.map_source (mem_chart_source _ _)⟩, ?_⟩
    change (p.1.val, d.symm (d p.2)) ∈ S
    rwa [d.left_inv (mem_chart_source _ _)]
  have hCp : (C (p.1.val, p.2)).IsInvertible := by
    dsimp only [C, pullbackVerticalCoframe]
    rw [hfeq p.1]
    exact (c.invertible_coframe _ (hVc hp)).comp
      (ContinuousLinearMap.IsInvertible.of_inverse
        (marking_mfderiv_inverse_right M N (e p.1) p.2)
        (marking_mfderiv_inverse_left M N (e p.1) p.2))
  have hpW : (p.1.val, d p.2) ∈ W := by
    refine ⟨hpD, ?_⟩
    change ((C (p.1.val, d.symm (d p.2))).comp
      (M.inverseChartTangentMap a (d p.2))).IsInvertible
    rw [d.left_inv (mem_chart_source _ _)]
    exact hCp.comp (inverseChartTangentMap_isInvertible M a (d p.2)
      (d.map_source (mem_chart_source _ _)))
  let U := intrinsicParameterChartDomain M a W
  have hUS : U ⊆ S := by
    intro q hq
    have h := hq.2.1.2
    change (q.1, d.symm (d q.2)) ∈ S at h
    rwa [d.left_inv hq.1.2] at h
  have hi : ∀ q ∈ U, (C q).IsInvertible := by
    intro q hq
    have hA : (A (q.1, d q.2)).IsInvertible := hq.2.2
    have he : (A (q.1, d q.2)).comp (M.chartTangentMap a q.2) = C q := by
      dsimp only [A]
      rw [d.left_inv hq.1.2]
      have h := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).symm_comp_deriv hq.1.2
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L => C q (L v)) h
    rw [← he]
    exact hA.comp (chartTangentMap_isInvertible M a q.2 hq.1.2)
  have hs : IsSmoothVerticalCoframeOn M C U :=
    fun b => (hC b).mono (fun q hq => ⟨hq.1, hUS hq.2⟩)
  refine ⟨⟨U, isOpen_intrinsicParameterChartDomain M a hW, C, hs, hi, ?_⟩,
    ⟨⟨mem_univ _, mem_chart_source _ _⟩, hpW⟩, hUS, rfl⟩
  intro q hq ht v
  dsimp only [C, pullbackVerticalCoframe]
  rw [hfeq ⟨q.1, ht⟩]
  have hJ : intervalPullbackAlmostComplex M N e J q.1 =
      pullbackAlmostComplex M N (e ⟨q.1, ht⟩) (J q.1) :=
    intervalPullbackAlmostComplex_apply M N e J ⟨q.1, ht⟩
  rw [hJ]
  change c.coframe (q.1, e ⟨q.1, ht⟩ q.2)
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (e ⟨q.1, ht⟩) q.2
      (pullbackAlmostComplex M N (e ⟨q.1, ht⟩) (J q.1) q.2 v)) = _
  rw [pullbackAlmostComplex_intertwines]
  apply c.intertwines_coframe _ (hVc ?_) ht
  have h := (hUS hq).2
  change (q.1, f q.1 q.2) ∈ V at h
  rwa [hfeq ⟨q.1, ht⟩] at h

/-- Totalize one actual target-valued real germ without changing any interval
map. This raw extension is smooth only on this point's own real-open set;
no common smooth extension of the interval family is asserted. -/
theorem exists_intervalMapExtension_germ {n : ℕ}
    (M N : SmoothManifold (2 * n)) (e : Parameter → M.SmoothEquiv N)
    (he : HasSmoothManifoldTargetFamilyOn M N univ (fun t x => e t x))
    (p : Parameter × M.Point) :
    ∃ (f : ℝ → M.Point → N.Point) (R : Set (ℝ × M.Point)), IsOpen R ∧
      intervalParameterInclusion M p ∈ R ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model (2 * n)) ∞ (fun q : ℝ × M.Point => f q.1 q.2) R ∧
      ∀ t : Parameter, f t.val = e t := by
  obtain ⟨U, hpU, β, hβ, heq⟩ := he p.1 (mem_univ _) p.2
  let f : ℝ → M.Point → N.Point := fun t x =>
    if ht : t ∈ parameterInterval then e ⟨t, ht⟩ x
    else if hU : (t, x) ∈ U then β ⟨(t, x), hU⟩ else e parameterZero x
  have hfeq : ∀ t : Parameter, f t.val = e t := by
    intro t
    funext x
    dsimp only [f]
    rw [dite_eq_left (show t.val ∈ parameterInterval from t.property)]
  have hrestrict : (fun q : U => f q.val.1 q.val.2) = β := by
    funext q
    dsimp only [f]
    split
    · rename_i ht
      exact (heq ⟨q.val.1, ht⟩ (mem_univ _) q.val.2 q.property).symm
    · rw [dite_eq_left q.property]
  refine ⟨f, U, U.isOpen, hpU, ?_, hfeq⟩
  have h : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun q : U => f q.val.1 q.val.2) := by
    rw [hrestrict]
    exact hβ
  intro q hq
  exact (contMDiffAt_subtype_iff (f := fun z : ℝ × M.Point => f z.1 z.2)
    (x := (⟨q, hq⟩ : U))).mp (h ⟨q, hq⟩) |>.contMDiffWithinAt

namespace MaslovFamily

/-- Coframes from individual real map germs supply local smooth complex
endomorphism extensions of the specified interval pullback. -/
theorem localSmoothComplexExtensions_intervalPullback_of_localGerms {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (he : HasSmoothManifoldTargetFamilyOn M N univ (fun t x => e t x)) :
    HasLocalSmoothIntervalComplexExtensions M (intervalPullbackAlmostComplex M N e h.J) := by
  intro p
  obtain ⟨f, R, hR, hRp, hf, hfeq⟩ := exists_intervalMapExtension_germ M N e he p
  obtain ⟨c, hpc⟩ := h.exists_intervalCanonicalChart (p.1, e p.1 p.2)
  obtain ⟨c', hp, _, _⟩ := exists_intervalCanonicalChart_pullback_at M N e f hR hf
    hfeq c c.isOpen_domain (Subset.refl _) p hRp hpc
  refine ⟨c'.domain, c'.isOpen_domain, hp,
    fun q => (c'.coframe q).inverse.comp
      ((coordinateComplexStructure n).comp (c'.coframe q)),
    c'.smooth_coframe.complexEndomorphism c'.invertible_coframe, ?_⟩
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  apply (c'.invertible_coframe _ hz).injective
  change c'.coframe (intervalParameterInclusion M z)
    ((c'.coframe (intervalParameterInclusion M z)).inverse
      (coordinateComplexStructure n (c'.coframe (intervalParameterInclusion M z) v))) = _
  rw [(c'.invertible_coframe _ hz).self_apply_inverse]
  exact (c'.intertwines_coframe _ hz z.1.property v).symm

/-- The actual pulled section has local smooth scalar coefficients in the
coframe transported through the same individual real germ. -/
theorem localSmoothTensorCoefficients_intervalPullback_of_localGerms {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (he : HasSmoothManifoldTargetFamilyOn M N univ (fun t x => e t x)) :
    HasLocalSmoothIntervalTensorCoefficients M (intervalPullbackAlmostComplex M N e h.J)
      (h.intervalPullbackTensorSection e) := by
  have ht := h.localSmoothIntervalTensorCoefficients h.intervalTensorSection
    (fun p => (congrArg Subtype.val (h.canonicalSquareMap_intervalTensorSection p)).symm)
  intro p
  obtain ⟨f, R, hR, hRp, hf, hfeq⟩ := exists_intervalMapExtension_germ M N e he p
  obtain ⟨c, U, hU, hUc, hpU, q, hq, hqe⟩ := ht (p.1, e p.1 p.2)
  obtain ⟨c', hp, hdomain, hcoframe⟩ := exists_intervalCanonicalChart_pullback_at M N e f
    hR hf hfeq c hU hUc p hRp hpU
  let F := fun z : ℝ × M.Point => (z.1, f z.1 z.2)
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ F R := contMDiffOn_fst.prodMk hf
  refine ⟨c', c'.domain, c'.isOpen_domain, Subset.refl _, hp,
    q ∘ F, hq.comp (hF.mono (fun z hz => (hdomain hz).1))
      (fun z hz => (hdomain hz).2), ?_⟩
  intro z hz
  have hzU : intervalParameterInclusion N (z.1, e z.1 z.2) ∈ U := by
    have H := (hdomain hz).2
    change (z.1.val, f z.1.val z.2) ∈ U at H
    rwa [hfeq z.1] at H
  change q (z.1.val, f z.1.val z.2) = _
  rw [hfeq z.1]
  change q (intervalParameterInclusion N (z.1, e z.1 z.2)) = _
  rw [hqe (z.1, e z.1 z.2) hzU]
  rw [← c.coefficient_squareMap, ← c'.coefficient_squareMap,
    h.canonicalSquareMap_intervalPullbackTensorSection]
  have htarget := congrArg Subtype.val
    (h.canonicalSquareMap_intervalTensorSection (z.1, e z.1 z.2))
  rw [htarget, hcoframe]
  dsimp only [pullbackVerticalCoframe, intervalParameterInclusion]
  rw [hfeq z.1]
  symm
  exact squaredCoframeCoefficient_comp _ _
    (ContinuousLinearMap.IsInvertible.of_inverse
      (marking_mfderiv_inverse_right M N (e z.1) z.2)
      (marking_mfderiv_inverse_left M N (e z.1) z.2)) _

/-- Local forward germs supply both regularity inputs for the actual
pulled interval complex field and actual canonical tensor-square section. -/
theorem localSmoothExtensions_intervalPullback_of_localGerms {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (he : HasSmoothManifoldTargetFamilyOn M N univ (fun t x => e t x)) :
    HasLocalSmoothIntervalComplexExtensions M (intervalPullbackAlmostComplex M N e h.J) ∧
    HasLocalSmoothIntervalTensorCoefficients M (intervalPullbackAlmostComplex M N e h.J)
      (h.intervalPullbackTensorSection e) :=
  ⟨h.localSmoothComplexExtensions_intervalPullback_of_localGerms e he,
    h.localSmoothTensorCoefficients_intervalPullback_of_localGerms e he⟩

end MaslovFamily

namespace GradedPairDeformation

/-- Actual pointwise real forward germs transport a given Maslov family
onto the same specified completed pair deformation. The pulled two-form
and marked endpoint equations remain explicit conditional hypotheses. -/
theorem exists_of_localGermPullback {n : ℕ} {D : PairDeformation n}
    {source : D.source.Maslov} {target : D.target.Maslov}
    (N : SmoothManifold (2 * n)) {etaN : ℝ → N.Form 2}
    (h : MaslovFamily N etaN)
    (e : Parameter → D.source.ambientManifold.SmoothEquiv N)
    (he : HasSmoothManifoldTargetFamilyOn D.source.ambientManifold N univ (fun t x => e t x))
    (eta : ℝ → D.source.ambientManifold.Form 2)
    (heta : ∀ t : Parameter, eta t.val =
      D.source.ambientManifold.exteriorDerivative (D.completedPrimitive t))
    (hform : ∀ t : Parameter, D.source.ambientManifold.pullback N (e t) (etaN t.val) =
      eta t.val)
    (hJ₀ : pullbackAlmostComplex D.source.ambientManifold N (e parameterZero) (h.J 0) =
      pullbackAlmostComplex D.source.ambientManifold D.source.ambientManifold
        (D.ambientCompletionPresentation parameterZero).equiv source.J)
    (hJ₁ : pullbackAlmostComplex D.source.ambientManifold N (e parameterOne) (h.J 1) =
      pullbackAlmostComplex D.source.ambientManifold D.target.ambientManifold
        (D.ambientCompletionPresentation parameterOne).equiv target.J)
    (hs₀ : pullbackSquaredTensor D.source.ambientManifold N
      (e parameterZero) (h.tensor 0) =
      pullbackSquaredTensor D.source.ambientManifold D.source.ambientManifold
        (D.ambientCompletionPresentation parameterZero).equiv source.tensor)
    (hs₁ : pullbackSquaredTensor D.source.ambientManifold N
      (e parameterOne) (h.tensor 1) =
      pullbackSquaredTensor D.source.ambientManifold D.target.ambientManifold
        (D.ambientCompletionPresentation parameterOne).equiv target.tensor) :
    ∃ g : GradedPairDeformation D source target,
      (∀ t : Parameter, g.family.J t.val =
        pullbackAlmostComplex D.source.ambientManifold N (e t) (h.J t.val)) ∧
      ∀ t : Parameter, g.family.tensor t.val =
        pullbackSquaredTensor D.source.ambientManifold N (e t) (h.tensor t.val) := by
  let J := intervalPullbackAlmostComplex D.source.ambientManifold N e h.J
  have hcompatible : ∀ t ∈ parameterInterval,
      IsCompatibleAlmostComplex D.source.ambientManifold (eta t) (J t) := by
    intro t ht
    dsimp only [J]
    rw [intervalPullbackAlmostComplex_apply D.source.ambientManifold N e h.J ⟨t, ht⟩,
      ← hform ⟨t, ht⟩]
    exact isCompatibleAlmostComplex_pullback D.source.ambientManifold N (e ⟨t, ht⟩)
      (etaN t) (h.J t) (h.compatible t ht)
  obtain ⟨g, hgJ, hgt⟩ := exists_of_localExtensions eta heta J hcompatible
    (h.localSmoothComplexExtensions_intervalPullback_of_localGerms e he)
    (h.intervalPullbackTensorSection e) (h.intervalPullbackTensorSection_ne_zero e)
    (h.localSmoothTensorCoefficients_intervalPullback_of_localGerms e he) (by
      change intervalPullbackAlmostComplex D.source.ambientManifold N e h.J
        parameterZero.val = _
      rw [intervalPullbackAlmostComplex_apply]
      exact hJ₀) (by
      change intervalPullbackAlmostComplex D.source.ambientManifold N e h.J
        parameterOne.val = _
      rw [intervalPullbackAlmostComplex_apply]
      exact hJ₁) (fun x =>
      (h.canonicalSquareMap_intervalPullbackTensorSection e (parameterZero, x)).trans
        (congrFun hs₀ x)) (fun x =>
      (h.canonicalSquareMap_intervalPullbackTensorSection e (parameterOne, x)).trans
        (congrFun hs₁ x))
  refine ⟨g, ?_, ?_⟩
  · intro t
    exact (hgJ t).trans (intervalPullbackAlmostComplex_apply D.source.ambientManifold N e h.J t)
  · intro t
    funext x
    exact (hgt (t, x)).trans (h.canonicalSquareMap_intervalPullbackTensorSection e (t, x))

end GradedPairDeformation

end FsFltz.Geometry
