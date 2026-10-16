import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCanonicalBundle
import FsFltz.Geometry.IntrinsicNativeCompletionEndCanonicalBundle

/-!
# Mixed canonical-square coordinates on the original completion

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. Mixed overlaps are the positive inward collar,
`0 < τ < δ`; radius is `-τ`. The original attachment maps, their actual
differentials, and the real mixed germs determine the transition. No mixed
derivative law or canonical transition is supplied as an assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

local instance mixedCanonicalBandCharts : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance mixedCanonicalProductCharts : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance mixedCanonicalProductSmooth : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

variable {δ : ℝ} (hδ : 0 < δ)
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

include hC hinv in
/-- Differentiating equality of the actual attachment maps computes the
mixed chart differential. The end chart keeps the outward-radius sign. -/
theorem originalMixedCanonicalDifferential_of_germ
    (a : IntrinsicInterior.Point k M) (b : IntrinsicBoundary.Point k M × ℝ)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (F : (Model k × ℝ) → IntrinsicInterior.Point k M)
    (hF : ContMDiffAt 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) ∞ F
      (chartAt (Model k × ℝ) b (endBandCoordinates p)))
    (hb : endBandCoordinates p ∈ (chartAt (Model k × ℝ) b).source)
    (ha : F (chartAt (Model k × ℝ) b (endBandCoordinates p)) ∈
      (chartAt (Model (k + 1)) a).source)
    (heq : ∀ᶠ q in 𝓝 p,
      interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
        (F (chartAt (Model k × ℝ) b (endBandCoordinates q))) =
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) q) :
    originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a
      (F (chartAt (Model k × ℝ) b (endBandCoordinates p))) =
      (fderiv ℝ ((chartAt (Model (k + 1)) a) ∘ F)
        (chartAt (Model k × ℝ) b (endBandCoordinates p))).comp
          (originalEndCanonicalDifferential hδ C hemb hboundary hzero b p) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let i := interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
  let j := cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
  let e := chartAt (Model k × ℝ) b
  let w := F (e (endBandCoordinates p))
  let B := (originalEndChartDifferential b (endBandCoordinates p)).comp
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p)
  have hi := isInvertible_mfderiv_completionInterior hδ C hemb hC hboundary hinv hzero w
  have hj := isInvertible_mfderiv_completionCylinder hδ C hemb hC hboundary hinv hzero p
  have hdE : MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ)
      (e ∘ endBandCoordinates) p :=
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) b).mdifferentiableAt hb).comp p
      (contMDiff_endBandCoordinates.mdifferentiableAt (by simp))
  have hdF := hF.mdifferentiableAt (by simp)
  have hdI := (contMDiff_completionInterior hδ C hemb hC hboundary hinv hzero).mdifferentiableAt
    (by simp) (x := w)
  have hdJ : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p =
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).comp
        ((mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) F
          (e (endBandCoordinates p))).comp B) := by
    have heq' : i ∘ F ∘ e ∘ endBandCoordinates =ᶠ[𝓝 p] j := heq
    have h := heq'.mfderiv_eq (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, Model (k + 1)))
    rw [mfderiv_comp p hdI (hdF.comp p hdE), mfderiv_comp p hdF hdE,
      mfderiv_comp p ((mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) b).mdifferentiableAt hb)
        (contMDiff_endBandCoordinates.mdifferentiableAt (by simp))] at h
    exact h.symm
  have hd : fderiv ℝ ((chartAt (Model (k + 1)) a) ∘ F) (e (endBandCoordinates p)) =
      (originalInteriorChartDifferential a w).comp
        (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) F
          (e (endBandCoordinates p))) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp _
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) a).mdifferentiableAt ha) hdF
  have hcancel : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) F
      (e (endBandCoordinates p))).comp B =
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).inverse.comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p) := by
    rw [hdJ]
    apply ContinuousLinearMap.ext
    intro v
    exact (hi.inverse_apply_self _).symm
  rw [hd]
  change (originalInteriorChartDifferential a w).comp
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).inverse =
    ((originalInteriorChartDifferential a w).comp
      (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) F
        (e (endBandCoordinates p)))).comp
      (B.comp (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse)
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) F _) B _, hcancel]
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (originalInteriorChartDifferential a w)
    (congrArg ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).inverse)
      (hj.self_apply_inverse v)).symm

include hC hinv in
/-- The actual mixed derivative cancels in the determinant square. Native
tangents use `N`; the real end chart uses the distinct normalization `PE`. -/
theorem originalMixedCanonical_squaredTransition_of_germ
    (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (a : IntrinsicInterior.Point k M) (b : IntrinsicBoundary.Point k M × ℝ)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (F : (Model k × ℝ) → IntrinsicInterior.Point k M)
    (hF : ContMDiffAt 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) ∞ F
      (chartAt (Model k × ℝ) b (endBandCoordinates p)))
    (hb : endBandCoordinates p ∈ (chartAt (Model k × ℝ) b).source)
    (ha : F (chartAt (Model k × ℝ) b (endBandCoordinates p)) ∈
      (chartAt (Model (k + 1)) a).source)
    (heq : ∀ᶠ q in 𝓝 p,
      interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
        (F (chartAt (Model k × ℝ) b (endBandCoordinates q))) =
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) q)
    (CI : Model (k + 1) →L[ℝ] TangentCoordinates n)
    (CE : (Model k × ℝ) →L[ℝ] TangentCoordinates n) :
    squaredCoframeTransition
      ((CI.comp (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a
        (F (chartAt (Model k × ℝ) b (endBandCoordinates p))))).comp N.toContinuousLinearMap)
      ((CE.comp (originalEndCanonicalDifferential hδ C hemb hboundary hzero b p)).comp N.toContinuousLinearMap) =
    squaredCoframeTransition
      ((CI.comp (fderiv ℝ ((chartAt (Model (k + 1)) a) ∘ F)
        (chartAt (Model k × ℝ) b (endBandCoordinates p)))).comp PE.toContinuousLinearMap)
      (CE.comp PE.toContinuousLinearMap) := by
  let HI := originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a
    (F (chartAt (Model k × ℝ) b (endBandCoordinates p)))
  let HE := originalEndCanonicalDifferential hδ C hemb hboundary hzero b p
  let L := fderiv ℝ ((chartAt (Model (k + 1)) a) ∘ F)
    (chartAt (Model k × ℝ) b (endBandCoordinates p))
  have hHE : HE.IsInvertible :=
    isInvertible_originalEndCanonicalDifferential hδ C hemb hC hboundary hinv hzero b p hb
  have hHI : HI = L.comp HE :=
    originalMixedCanonicalDifferential_of_germ hδ C hemb hC hboundary hinv hzero a b p F hF hb ha heq
  let A := PE.symm.toContinuousLinearMap.comp (HE.comp N.toContinuousLinearMap)
  have hA : A.IsInvertible :=
    (show PE.symm.toContinuousLinearMap.IsInvertible from ⟨PE.symm, rfl⟩).comp
      (hHE.comp ⟨N, rfl⟩)
  have h := squaredCoframeTransition_comp ((CI.comp L).comp PE.toContinuousLinearMap)
    (CE.comp PE.toContinuousLinearMap) A hA
  change squaredCoframeTransition ((CI.comp HI).comp N.toContinuousLinearMap)
    ((CE.comp HE).comp N.toContinuousLinearMap) = _
  rw [hHI]
  convert h using 1
  · congr 1 <;> ext v <;>
      simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]

/-- Spatial differentiation of a real parameter family uses the spatial
inclusion into its product domain, so it introduces no time slot. -/
def mixedSpatialDerivative {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ × E → F) (z : ℝ × E) : E →L[ℝ] F :=
  (fderiv ℝ g z).comp (ContinuousLinearMap.inr ℝ ℝ E)

theorem mixedSpatialDerivative_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ × E → F} {z : ℝ × E}
    (hg : DifferentiableAt ℝ g z) :
    mixedSpatialDerivative g z = fderiv ℝ (fun y => g (z.1, y)) z.2 := by
  exact (hg.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv.symm

theorem contDiffOn_mixedSpatialDerivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × E → F} {U : Set (ℝ × E)} (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (mixedSpatialDerivative g) U :=
  (hg.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const

end FsFltz.Geometry.IntrinsicCompletionGluing
