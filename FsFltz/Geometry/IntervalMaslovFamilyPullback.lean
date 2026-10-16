import FsFltz.Geometry.IntervalMaslovTransport
import FsFltz.Geometry.MaslovPullback

/-!
# Grading pullback by a jointly smooth interval family

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. Maps are diffeomorphisms only on the prescribed
parameter interval. Genuine smooth forward-map extensions transport local
coframes; inversion of their spatial differentials supplies the local complex
endomorphism extensions. No inverse-map equations or compatibility conditions
are imposed outside the interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct Classical
open Set Filter Bundle

namespace FsFltz.Geometry

namespace IsSmoothVerticalCoframeOn

/-- Smooth inversion of an actual vertical coframe gives a smooth
endomorphism field, with the usual spatial tangent transition maps. -/
theorem complexEndomorphism {n : ℕ} {M : SmoothManifold (2 * n)}
    {U : Set (ℝ × M.Point)}
    {C : (ℝ × M.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : IsSmoothVerticalCoframeOn M C U)
    (hinv : ∀ p ∈ U, (C p).IsInvertible) :
    IsSmoothVerticalEndomorphismOn M
      (fun p => (C p).inverse.comp ((coordinateComplexStructure n).comp (C p))) U := by
  intro b
  let e := chartAt (Model (2 * n)) b
  let D := intrinsicParameterCoordinateDomain M b U
  let A := fun p : ℝ × Model (2 * n) =>
    (C (p.1, e.symm p.2)).comp (M.inverseChartTangentMap b p.2)
  have hi : ∀ p ∈ D, (A p).IsInvertible := by
    intro p hp
    exact (hinv _ hp.2).comp (inverseChartTangentMap_isInvertible M b p.2 hp.1.2)
  apply ((contDiffOn_coframe_inverse (hC b) hi).clm_comp
    ((contDiffOn_const (c := coordinateComplexStructure n)).clm_comp (hC b))).congr
  intro p hp
  have hchart := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).comp_symm_deriv
    hp.1.2
  have hinverse : (M.inverseChartTangentMap b p.2).inverse =
      M.chartTangentMap b (e.symm p.2) := by
    apply ContinuousLinearMap.inverse_eq
    · have h := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).symm_comp_deriv
        (e.map_target hp.1.2)
      rwa [e.right_inv hp.1.2] at h
    · exact hchart
  dsimp only [A]
  have hCi : (C (p.1, e.symm p.2)).IsInvertible := hinv _ hp.2
  rw [hCi.inverse_comp_of_left, hinverse]
  ext v
  rfl

end IsSmoothVerticalCoframeOn

/-- Pullback of a raw vertical coframe uses only the spatial derivative. -/
def pullbackVerticalCoframe {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : ℝ → M.Point → N.Point)
    (C : (ℝ × N.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (p : ℝ × M.Point) : Model (2 * n) →L[ℝ] TangentCoordinates n :=
  (C (p.1, f p.1 p.2)).comp
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (f p.1) p.2)

/-- Joint smoothness of maps gives joint smoothness of their coframe
pullback on the genuine open preimage domain. The derivative is the
vertical restriction of the joint chart derivative. -/
theorem isSmoothVerticalCoframeOn_pullback {n : ℕ}
    (M N : SmoothManifold (2 * n)) (f : ℝ → M.Point → N.Point)
    {R : Set (ℝ × M.Point)} (hR : IsOpen R)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × M.Point => f p.1 p.2) R)
    {U : Set (ℝ × N.Point)} (hU : IsOpen U)
    (C : (ℝ × N.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (hC : IsSmoothVerticalCoframeOn N C U) :
    IsSmoothVerticalCoframeOn M (pullbackVerticalCoframe M N f C)
      (R ∩ (fun p : ℝ × M.Point => (p.1, f p.1 p.2)) ⁻¹' U) := by
  intro a p hp
  let c := chartAt (Model (2 * n)) a
  let x := c.symm p.2
  let b := chartAt (Model (2 * n)) (f p.1 x)
  let q₀ : ℝ × Model (2 * n) → ℝ × M.Point := fun z => (z.1, c.symm z.2)
  have hq₀ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ q₀ (univ ×ˢ c.target) :=
    contMDiffOn_fst.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := a)).comp
        contMDiffOn_snd (fun _ hz => hz.2))
  let W := (univ ×ˢ c.target) ∩ q₀ ⁻¹' R
  have hW : IsOpen W := hq₀.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) hR
  let k := fun z : ℝ × Model (2 * n) => f z.1 (c.symm z.2)
  have hk : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ k W :=
    hf.comp (hq₀.mono inter_subset_left) inter_subset_right
  let S := W ∩ k ⁻¹' b.source
  have hS : IsOpen S := hk.continuousOn.isOpen_inter_preimage hW b.open_source
  have hpS : p ∈ S := ⟨⟨hp.1, hp.2.1⟩, mem_chart_source _ _⟩
  let g := fun z : ℝ × Model (2 * n) => b (k z)
  have hgm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ g S :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := f p.1 x)).comp
      (hk.mono inter_subset_left) inter_subset_right
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g S := hgm.contDiffOn
  let q := fun z : ℝ × Model (2 * n) => (z.1, g z)
  have hq : ContDiffOn ℝ ∞ q S := contDiffOn_fst.prodMk hg
  let T := S ∩ q ⁻¹' intrinsicParameterCoordinateDomain N (f p.1 x) U
  have hT : IsOpen T := hq.continuousOn.isOpen_inter_preimage hS
    (isOpen_intrinsicParameterCoordinateDomain N (f p.1 x) hU)
  have hpT : p ∈ T := by
    refine ⟨hpS, ⟨mem_univ _, b.map_source (mem_chart_source _ _)⟩, ?_⟩
    change (p.1, b.symm (b (f p.1 x))) ∈ U
    rw [b.left_inv (mem_chart_source _ _)]
    exact hp.2.2
  have hcoeff := (hC (f p.1 x)).comp (hq.mono inter_subset_left) inter_subset_right
  let B := fun z : ℝ × Model (2 * n) =>
    (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ (Model (2 * n)))
  have hB : ContDiffOn ℝ ∞ B T :=
    ((hg.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_comp contDiffOn_const).mono
      inter_subset_left
  apply (((hcoeff.clm_comp hB).contDiffAt (hT.mem_nhds hpT)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hT.mem_nhds hpT] with z hz
  have hd : DifferentiableAt ℝ g z :=
    (hg.contDiffAt (hS.mem_nhds hz.1)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun y : Model (2 * n) => (z.1, y))
      (ContinuousLinearMap.inr ℝ ℝ (Model (2 * n))) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have hsp : fderiv ℝ (fun y => g (z.1, y)) z.2 = B z := by
    exact (hd.hasFDerivAt.comp z.2 hc).fderiv
  have hfa : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      (f z.1) (c.symm z.2) :=
    (((hf.contMDiffAt (hR.mem_nhds hz.1.1.2)).comp (c.symm z.2)
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
  have hca := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt_symm
    hz.1.1.1.2
  have hcb := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) (f p.1 x)).mdifferentiableAt
    hz.1.2
  have hforward : B z = (N.chartTangentMap (f p.1 x) (f z.1 (c.symm z.2))).comp
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (f z.1) (c.symm z.2)).comp
        (M.inverseChartTangentMap a z.2)) := by
    rw [← hsp, ← mfderiv_eq_fderiv]
    erw [mfderiv_comp z.2 hcb (hfa.comp z.2 hca), mfderiv_comp z.2 hfa hca]
    rfl
  have hinverse := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) (f p.1 x)).symm_comp_deriv
    hz.1.2
  change (pullbackVerticalCoframe M N f C (z.1, c.symm z.2)).comp
      (M.inverseChartTangentMap a z.2) =
    ((C (z.1, b.symm (g z))).comp
      (N.inverseChartTangentMap (f p.1 x) (g z))).comp (B z)
  rw [hforward]
  have hb : b.symm (g z) = f z.1 (c.symm z.2) := b.left_inv hz.1.2
  rw [hb]
  apply ContinuousLinearMap.ext
  intro v
  exact (congrArg (fun L => C (z.1, f z.1 (c.symm z.2))
    (L (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (f z.1)
      (c.symm z.2) (M.inverseChartTangentMap a z.2 v)))) hinverse).symm

/-- A raw real-indexed field whose interval values are exactly the
pullback through the prescribed interval diffeomorphisms. -/
def intervalPullbackAlmostComplex {n : ℕ} (M N : SmoothManifold (2 * n))
    (e : Parameter → M.SmoothEquiv N) (J : ℝ → AlmostComplexField N)
    (t : ℝ) : AlmostComplexField M :=
  if ht : t ∈ parameterInterval then pullbackAlmostComplex M N (e ⟨t, ht⟩) (J t) else 0

@[simp] theorem intervalPullbackAlmostComplex_apply {n : ℕ}
    (M N : SmoothManifold (2 * n)) (e : Parameter → M.SmoothEquiv N)
    (J : ℝ → AlmostComplexField N) (t : Parameter) :
    intervalPullbackAlmostComplex M N e J t.val =
      pullbackAlmostComplex M N (e t) (J t.val) := by
  unfold intervalPullbackAlmostComplex
  split
  · rfl
  · rename_i h
    exact (h t.property).elim

/-- Local interval coframes pull back along a genuine smooth map extension.
Openness of invertibility supplies the source neighborhood. Only the
interval maps are required to be diffeomorphisms. -/
theorem exists_intervalCanonicalChart_pullback {n : ℕ}
    (M N : SmoothManifold (2 * n)) (e : Parameter → M.SmoothEquiv N)
    (f : ℝ → M.Point → N.Point)
    {R : Set (ℝ × M.Point)} (hR : IsOpen R)
    (hRcover : parameterInterval ×ˢ univ ⊆ R)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × M.Point => f p.1 p.2) R)
    (hfeq : ∀ t : Parameter, f t.val = e t)
    {J : ℝ → AlmostComplexField N} (c : IntervalCanonicalChart N J)
    {V : Set (ℝ × N.Point)} (hV : IsOpen V) (hVc : V ⊆ c.domain)
    (p : Parameter × M.Point) (hp : (p.1.val, e p.1 p.2) ∈ V) :
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
    refine ⟨hRcover ⟨p.1.property, mem_univ _⟩, ?_⟩
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

namespace MaslovFamily

/-- The original compatible interval complex field pulls back with genuine
local smooth endomorphism extensions. Forward-map regularity suffices:
the local coframe differential is inverted on its open invertibility locus. -/
theorem localSmoothComplexExtensions_intervalPullback {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (he : M.IsSmoothIntervalMapFamily N (fun t => e t)) :
    HasLocalSmoothIntervalComplexExtensions M (intervalPullbackAlmostComplex M N e h.J) := by
  obtain ⟨f, ⟨R, hR, hRcover, hf⟩, hfeq⟩ := he
  intro p
  obtain ⟨c, hpc⟩ := h.exists_intervalCanonicalChart (p.1, e p.1 p.2)
  obtain ⟨c', hp, _, _⟩ := exists_intervalCanonicalChart_pullback M N e f hR hRcover hf
    hfeq c c.isOpen_domain (Subset.refl _) p hpc
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

/-- The pulled section is an actual element of the canonical tensor-square
fiber. Its tensor image is the derivative pullback of the original section. -/
def intervalPullbackTensorSection {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (p : Parameter × M.Point) :
    CanonicalTensorSquare (intervalPullbackAlmostComplex M N e h.J p.1.val p.2) :=
  (canonicalSquareEquivOfComplexStructure _ (by
    rw [intervalPullbackAlmostComplex_apply]
    exact (isCompatibleAlmostComplex_pullback M N (e p.1) (eta p.1.val)
      (h.J p.1.val) (h.compatible p.1.val p.1.property)).2.1 p.2)).symm
    ⟨pullbackSquaredTensor M N (e p.1) (h.tensor p.1.val) p.2, by
      rw [intervalPullbackAlmostComplex_apply]
      exact pullbackSquaredTensor_canonical M N (e p.1) (h.J p.1.val)
        (h.tensor p.1.val) (h.canonical p.1.val p.1.property) p.2⟩

theorem canonicalSquareMap_intervalPullbackTensorSection {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (p : Parameter × M.Point) :
    (canonicalSquareMap (intervalPullbackAlmostComplex M N e h.J p.1.val p.2)
      (h.intervalPullbackTensorSection e p)).val =
      pullbackSquaredTensor M N (e p.1) (h.tensor p.1.val) p.2 := by
  exact congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _ _).apply_symm_apply _)

theorem intervalPullbackTensorSection_ne_zero {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (p : Parameter × M.Point) : h.intervalPullbackTensorSection e p ≠ 0 := by
  intro hz
  have ht := h.canonicalSquareMap_intervalPullbackTensorSection e p
  rw [hz, map_zero, Submodule.coe_zero] at ht
  exact pullbackSquaredTensor_ne_zero M N (e p.1) (h.tensor p.1.val)
    (h.nowhereZero p.1.val p.1.property) p.2 ht.symm

/-- Local scalar extensions of the original section pull back through the
same joint map and spatial derivative. The resulting witnesses retain the
entire actual canonical-square section, including the endpoint values. -/
theorem localSmoothTensorCoefficients_intervalPullback {n : ℕ}
    {M N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (e : Parameter → M.SmoothEquiv N)
    (he : M.IsSmoothIntervalMapFamily N (fun t => e t)) :
    HasLocalSmoothIntervalTensorCoefficients M (intervalPullbackAlmostComplex M N e h.J)
      (h.intervalPullbackTensorSection e) := by
  obtain ⟨f, ⟨R, hR, hRcover, hf⟩, hfeq⟩ := he
  have ht := h.localSmoothIntervalTensorCoefficients h.intervalTensorSection
    (fun p => (congrArg Subtype.val (h.canonicalSquareMap_intervalTensorSection p)).symm)
  intro p
  obtain ⟨c, U, hU, hUc, hpU, q, hq, hqe⟩ := ht (p.1, e p.1 p.2)
  obtain ⟨c', hp, hdomain, hcoframe⟩ := exists_intervalCanonicalChart_pullback M N e f
    hR hRcover hf hfeq c hU hUc p hpU
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

end MaslovFamily

namespace GradedPairDeformation

/-- A jointly smooth family of specified diffeomorphisms transports an
ambient grading onto this very completed deformation. Compatibility follows
from the actual pulled two-form identity, while local coframe and scalar
extensions supply the regularity inputs of `exists_of_localExtensions`.
Every interval value and both prescribed completion presentations are kept. -/
theorem exists_of_intervalPullback {n : ℕ} {D : PairDeformation n}
    {source : D.source.Maslov} {target : D.target.Maslov}
    (N : SmoothManifold (2 * n)) {etaN : ℝ → N.Form 2}
    (h : MaslovFamily N etaN)
    (e : Parameter → D.source.ambientManifold.SmoothEquiv N)
    (he : D.source.ambientManifold.IsSmoothIntervalMapFamily N (fun t => e t))
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
    (h.localSmoothComplexExtensions_intervalPullback e he)
    (h.intervalPullbackTensorSection e) (h.intervalPullbackTensorSection_ne_zero e)
    (h.localSmoothTensorCoefficients_intervalPullback e he) (by
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
