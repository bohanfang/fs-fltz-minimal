import FsFltz.Geometry.IntervalMaslovFamilyPullback

/-!
# Local coordinate coframes through a genuine spatial derivative

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The coordinate target may have a different
model space from the completed ambient. Time is retained and only the
spatial derivative transports the coframe. This permits the original
boundary–radial cylinder model to supply actual local grading tensors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

/-- A coframe in local source coordinates transports through the actual
spatial derivative of the real map; no identification of the two models
is used. -/
def pullbackCoordinateVerticalCoframe {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : SmoothManifold (2 * n)) (f : ℝ × M.Point → F)
    (C : (ℝ × F) → F →L[ℝ] TangentCoordinates n)
    (p : ℝ × M.Point) : Model (2 * n) →L[ℝ] TangentCoordinates n :=
  (C (p.1, f p)).comp
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, F) (fun x => f (p.1, x)) p.2)

/-- Conjugation of the source coframe-induced complex structure through
the actual spatial derivative is the complex structure of the pulled
coframe. The source tangent model may be a boundary–radial product. -/
theorem coframeComplexStructure_coordinateComp {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : F →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (A : Model (2 * n) →L[ℝ] F) :
    coframeComplexStructure (C.comp A) =
      A.inverse.comp ((C.inverse.comp ((coordinateComplexStructure n).comp C)).comp A) := by
  unfold coframeComplexStructure
  rw [hC.inverse_comp_of_left]
  ext v
  rfl

/-- An original source complex structure represented by its coframe is
transported literally through the same spatial derivative. -/
theorem coframeComplexStructure_coordinateComp_eq {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : F →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (A : Model (2 * n) →L[ℝ] F) (J : F →L[ℝ] F)
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    coframeComplexStructure (C.comp A) = A.inverse.comp (J.comp A) := by
  rw [coframeComplexStructure_coordinateComp C hC A]
  have hJ : C.inverse.comp ((coordinateComplexStructure n).comp C) = J := by
    ext v
    change C.inverse (coordinateComplexStructure n (C v)) = J v
    rw [← hCJ, hC.inverse_apply_self]
  rw [hJ]

/-- The complete squared tensor pulls back by the same spatial derivative,
including its scalar coefficient. No equality of tangent models is needed. -/
theorem smul_coframeSquaredGenerator_coordinateComp {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : F →L[ℝ] TangentCoordinates n)
    (A : Model (2 * n) →L[ℝ] F) (a : ℂ) :
    a • coframeSquaredGenerator (C.comp A) =
      (a • (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C)).compContinuousLinearMap
        (fun _ => A) := by
  ext v
  rfl

/-- Smooth local source coframes pull back smoothly by the vertical
restriction of the joint derivative. The source coordinate model is
arbitrary, in particular the native boundary–radial product model. -/
theorem isSmoothVerticalCoframeOn_coordinatePullback {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : SmoothManifold (2 * n)) (f : ℝ × M.Point → F)
    {R : Set (ℝ × M.Point)} (hR : IsOpen R)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, F) ∞ f R)
    {V : Set (ℝ × F)} (hV : IsOpen V)
    (C : (ℝ × F) → F →L[ℝ] TangentCoordinates n)
    (hC : ContDiffOn ℝ ∞ C V) :
    IsSmoothVerticalCoframeOn M (pullbackCoordinateVerticalCoframe M f C)
      (R ∩ (fun p : ℝ × M.Point => (p.1, f p)) ⁻¹' V) := by
  intro a p hp
  let c := chartAt (Model (2 * n)) a
  let q₀ : ℝ × Model (2 * n) → ℝ × M.Point := fun z => (z.1, c.symm z.2)
  have hq₀ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ q₀ (univ ×ˢ c.target) :=
    contMDiffOn_fst.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := a)).comp
        contMDiffOn_snd (fun _ hz => hz.2))
  let W := (univ ×ˢ c.target) ∩ q₀ ⁻¹' R
  have hW : IsOpen W := hq₀.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) hR
  let g := f ∘ q₀
  have hgm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, F) ∞ g W :=
    hf.comp (hq₀.mono inter_subset_left) inter_subset_right
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g W := hgm.contDiffOn
  let q := fun z : ℝ × Model (2 * n) => (z.1, g z)
  have hq : ContDiffOn ℝ ∞ q W := contDiffOn_fst.prodMk hg
  let T := W ∩ q ⁻¹' V
  have hT : IsOpen T := hq.continuousOn.isOpen_inter_preimage hW hV
  have hpT : p ∈ T := ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
  have hcoeff := hC.comp (hq.mono inter_subset_left) inter_subset_right
  let B := fun z : ℝ × Model (2 * n) =>
    (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ (Model (2 * n)))
  have hB : ContDiffOn ℝ ∞ B T :=
    ((hg.fderiv_of_isOpen (m := ∞) hW (by simp)).clm_comp contDiffOn_const).mono
      inter_subset_left
  apply (((hcoeff.clm_comp hB).contDiffAt (hT.mem_nhds hpT)).congr_of_eventuallyEq
    ?_).contDiffWithinAt
  filter_upwards [hT.mem_nhds hpT] with z hz
  have hd : DifferentiableAt ℝ g z :=
    (hg.contDiffAt (hW.mem_nhds hz.1)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun y : Model (2 * n) => (z.1, y))
      (ContinuousLinearMap.inr ℝ ℝ (Model (2 * n))) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have hsp : fderiv ℝ (fun y => g (z.1, y)) z.2 = B z :=
    (hd.hasFDerivAt.comp z.2 hc).fderiv
  have hfa : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, F)
      (fun y => f (z.1, y)) (c.symm z.2) :=
    (((hf.contMDiffAt (hR.mem_nhds hz.1.2)).comp (c.symm z.2)
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
  have hca := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt_symm
    hz.1.1.2
  have hforward : B z =
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, F) (fun y => f (z.1, y))
        (c.symm z.2)).comp (M.inverseChartTangentMap a z.2) := by
    rw [← hsp, ← mfderiv_eq_fderiv]
    exact mfderiv_comp z.2 hfa hca
  change ((C (z.1, f (z.1, c.symm z.2))).comp
    (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, F) (fun y => f (z.1, y))
      (c.symm z.2))).comp (M.inverseChartTangentMap a z.2) =
    (C (q z)).comp (B z)
  rw [hforward]
  rfl

namespace IsSmoothVerticalCoframeOn

/-- A smooth actual vertical coframe gives the smooth determinant square
in every spatial tangent chart. -/
theorem squaredGenerator {n : ℕ} {M : SmoothManifold (2 * n)}
    {U : Set (ℝ × M.Point)}
    {C : (ℝ × M.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : IsSmoothVerticalCoframeOn M C U) :
    IsSmoothVerticalSquaredTensorOn M (fun p => coframeSquaredGenerator (C p)) U := by
  intro b
  apply (contDiffOn_coframeSquaredGenerator (hC b)).congr
  intro p _
  ext v
  rfl

end IsSmoothVerticalCoframeOn

end FsFltz.Geometry
