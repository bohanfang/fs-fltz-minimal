import FsFltz.Geometry.IntrinsicNativeCompletionEndGradingDerivative
import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCanonicalChart

/-!
# Original cylindrical-end canonical coordinates

Source: `geoemtric-part-fsf.tex`, lines 119–122 (open smooth extension),
`def:maslov`, lines 212–232, and `sec:lean`, lines 788–814. The original
full cylinder supplies its actual tangent differential. The boundary–radius
coordinates retain the sign change from inward collar time to outward radius.
Both inclusion and sign-change differentials cancel on chart overlaps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

/-- The actual differential of an original boundary–radial chart. -/
def originalEndChartDifferential (a w : IntrinsicBoundary.Point k M × ℝ) :
    (Model k × ℝ) →L[ℝ] (Model k × ℝ) :=
  mfderiv 𝓘(ℝ, (Model k × ℝ)) 𝓘(ℝ, (Model k × ℝ))
    (chartAt ((Model k × ℝ)) a) w

theorem isInvertible_originalEndChartDifferential
    (a w : IntrinsicBoundary.Point k M × ℝ)
    (hw : w ∈ (chartAt ((Model k × ℝ)) a).source) :
    (originalEndChartDifferential a w).IsInvertible := by
  let A := mdifferentiable_chart (I := 𝓘(ℝ, (Model k × ℝ))) a
  apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (A.symm_comp_deriv hw)
  have h := A.comp_symm_deriv ((chartAt ((Model k × ℝ)) a).map_source hw)
  rwa [(chartAt ((Model k × ℝ)) a).left_inv hw] at h

/-- The inverse chart's derivative is the inverse actual chart differential. -/
theorem mfderiv_originalEndChart_symm
    (a w : IntrinsicBoundary.Point k M × ℝ)
    (hw : w ∈ (chartAt ((Model k × ℝ)) a).source) :
    mfderiv 𝓘(ℝ, (Model k × ℝ)) 𝓘(ℝ, (Model k × ℝ))
      (chartAt ((Model k × ℝ)) a).symm (chartAt ((Model k × ℝ)) a w) =
      (originalEndChartDifferential a w).inverse := by
  have hi := isInvertible_originalEndChartDifferential a w hw
  have h := (mdifferentiable_chart (I := 𝓘(ℝ, (Model k × ℝ))) a).symm_comp_deriv hw
  change (mfderiv 𝓘(ℝ, (Model k × ℝ)) 𝓘(ℝ, (Model k × ℝ))
    (chartAt ((Model k × ℝ)) a).symm (chartAt ((Model k × ℝ)) a w)).comp
      (originalEndChartDifferential a w) = ContinuousLinearMap.id ℝ ((Model k × ℝ)) at h
  ext v
  have he := congrArg (fun L : (Model k × ℝ) →L[ℝ] (Model k × ℝ) =>
    L ((originalEndChartDifferential a w).inverse v)) h
  change (mfderiv 𝓘(ℝ, (Model k × ℝ)) 𝓘(ℝ, (Model k × ℝ))
    (chartAt ((Model k × ℝ)) a).symm (chartAt ((Model k × ℝ)) a w))
      ((originalEndChartDifferential a w) ((originalEndChartDifferential a w).inverse v)) =
        (originalEndChartDifferential a w).inverse v at he
  rw [hi.self_apply_inverse] at he
  exact he

/-- Chart transition differentials come from the literal transition map. -/
theorem fderiv_originalEndChart_transition
    (a b w : IntrinsicBoundary.Point k M × ℝ)
    (ha : w ∈ (chartAt ((Model k × ℝ)) a).source)
    (hb : w ∈ (chartAt ((Model k × ℝ)) b).source) :
    fderiv ℝ ((chartAt ((Model k × ℝ)) b) ∘ (chartAt ((Model k × ℝ)) a).symm)
      (chartAt ((Model k × ℝ)) a w) =
      (originalEndChartDifferential b w).comp
        (originalEndChartDifferential a w).inverse := by
  rw [← mfderiv_eq_fderiv]
  have hs := (mdifferentiable_chart (I := 𝓘(ℝ, (Model k × ℝ))) a).symm
    |>.mdifferentiableAt ((chartAt ((Model k × ℝ)) a).map_source ha)
  have ht := (mdifferentiable_chart (I := 𝓘(ℝ, (Model k × ℝ))) b).mdifferentiableAt hb
  have h := mfderiv_comp (chartAt ((Model k × ℝ)) a w)
    (f := (chartAt ((Model k × ℝ)) a).symm) (g := chartAt ((Model k × ℝ)) b)
    (by simpa only [(chartAt ((Model k × ℝ)) a).left_inv ha] using ht) hs
  rw [(chartAt ((Model k × ℝ)) a).left_inv ha,
    mfderiv_originalEndChart_symm a w ha] at h
  exact h

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

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

/-- The actual end chart differential includes the original full cylinder
and its inward-time to outward-radius change. -/
def originalEndCanonicalDifferential (a : IntrinsicBoundary.Point k M × ℝ)
    (p : Band δ (IntrinsicBoundary.Point k M)) : Model (k + 1) →L[ℝ] (Model k × ℝ) :=
  letI := completionChartedSpace hδ C hemb hboundary hzero
  (originalEndChartDifferential a (endBandCoordinates p)).comp
    ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
        (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) p).inverse)

include hC hinv in
theorem isInvertible_originalEndCanonicalDifferential
    (a : IntrinsicBoundary.Point k M × ℝ) (p : Band δ (IntrinsicBoundary.Point k M))
    (hp : endBandCoordinates p ∈ (chartAt (Model k × ℝ) a).source) :
    (originalEndCanonicalDifferential hδ C hemb hboundary hzero a p).IsInvertible :=
  (isInvertible_originalEndChartDifferential a (endBandCoordinates p) hp).comp
    ((isInvertible_mfderiv_endBandCoordinates p).comp
      (isInvertible_mfderiv_completionCylinder hδ C hemb hC hboundary hinv hzero p).inverse)

include hC hinv in
/-- All actual cylinder and radius-change derivatives cancel, leaving the
literal original product-chart transition derivative. -/
theorem originalEndCanonicalDifferential_transition
    (a b : IntrinsicBoundary.Point k M × ℝ) (p : Band δ (IntrinsicBoundary.Point k M))
    (ha : endBandCoordinates p ∈ (chartAt (Model k × ℝ) a).source)
    (hb : endBandCoordinates p ∈ (chartAt (Model k × ℝ) b).source) :
    (originalEndCanonicalDifferential hδ C hemb hboundary hzero b p).comp
      (originalEndCanonicalDifferential hδ C hemb hboundary hzero a p).inverse =
      fderiv ℝ ((chartAt (Model k × ℝ) b) ∘ (chartAt (Model k × ℝ) a).symm)
        (chartAt (Model k × ℝ) a (endBandCoordinates p)) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let D := (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) p).inverse
  have hi : D.IsInvertible := (isInvertible_mfderiv_endBandCoordinates p).comp
    (isInvertible_mfderiv_completionCylinder hδ C hemb hC hboundary hinv hzero p).inverse
  have hai := isInvertible_originalEndChartDifferential a (endBandCoordinates p) ha
  rw [fderiv_originalEndChart_transition a b (endBandCoordinates p) ha hb]
  change ((originalEndChartDifferential b (endBandCoordinates p)).comp D).comp
    ((originalEndChartDifferential a (endBandCoordinates p)).comp D).inverse = _
  rw [hai.inverse_comp_of_left]
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (originalEndChartDifferential b (endBandCoordinates p))
    (hi.self_apply_inverse ((originalEndChartDifferential a (endBandCoordinates p)).inverse v))

include hC hinv in
/-- Native and end-coordinate normalization are distinct. Their common
actual spatial differential cancels from canonical-square transitions. -/
theorem originalEndCanonical_squaredTransition
    (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (a b : IntrinsicBoundary.Point k M × ℝ) (p : Band δ (IntrinsicBoundary.Point k M))
    (ha : endBandCoordinates p ∈ (chartAt (Model k × ℝ) a).source)
    (hb : endBandCoordinates p ∈ (chartAt (Model k × ℝ) b).source)
    (Ca Cb : (Model k × ℝ) →L[ℝ] TangentCoordinates n) :
    squaredCoframeTransition
      ((Cb.comp (originalEndCanonicalDifferential hδ C hemb hboundary hzero b p)).comp N.toContinuousLinearMap)
      ((Ca.comp (originalEndCanonicalDifferential hδ C hemb hboundary hzero a p)).comp N.toContinuousLinearMap) =
    squaredCoframeTransition
      ((Cb.comp (fderiv ℝ ((chartAt (Model k × ℝ) b) ∘
        (chartAt (Model k × ℝ) a).symm) (chartAt (Model k × ℝ) a (endBandCoordinates p)))).comp P.toContinuousLinearMap)
      (Ca.comp P.toContinuousLinearMap) := by
  let Ha := originalEndCanonicalDifferential hδ C hemb hboundary hzero a p
  let Hb := originalEndCanonicalDifferential hδ C hemb hboundary hzero b p
  let L := fderiv ℝ ((chartAt (Model k × ℝ) b) ∘ (chartAt (Model k × ℝ) a).symm)
    (chartAt (Model k × ℝ) a (endBandCoordinates p))
  have hi : Ha.IsInvertible :=
    isInvertible_originalEndCanonicalDifferential hδ C hemb hC hboundary hinv hzero a p ha
  have ht : Hb.comp Ha.inverse = L :=
    originalEndCanonicalDifferential_transition hδ C hemb hC hboundary hinv hzero a b p ha hb
  have hHb : Hb = L.comp Ha := by
    rw [← ht]
    apply ContinuousLinearMap.ext
    intro v
    exact (congrArg Hb (hi.inverse_apply_self v)).symm
  let A := P.symm.toContinuousLinearMap.comp (Ha.comp N.toContinuousLinearMap)
  have hAi : A.IsInvertible :=
    (show P.symm.toContinuousLinearMap.IsInvertible from ⟨P.symm, rfl⟩).comp
      (hi.comp ⟨N, rfl⟩)
  have he := squaredCoframeTransition_comp ((Cb.comp L).comp P.toContinuousLinearMap)
    (Ca.comp P.toContinuousLinearMap) A hAi
  change squaredCoframeTransition ((Cb.comp Hb).comp N.toContinuousLinearMap)
    ((Ca.comp Ha).comp N.toContinuousLinearMap) =
    squaredCoframeTransition ((Cb.comp L).comp P.toContinuousLinearMap)
      (Ca.comp P.toContinuousLinearMap)
  rw [hHb]
  convert he using 1
  · congr 1 <;> ext v <;>
      simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]

/-- The real spatial overlap of two original boundary–radial charts. -/
def originalEndCoordinateOverlap (a b : IntrinsicBoundary.Point k M × ℝ) : Set ((Model k × ℝ)) :=
  (chartAt ((Model k × ℝ)) a).target ∩
    (chartAt ((Model k × ℝ)) a).symm ⁻¹' (chartAt ((Model k × ℝ)) b).source

theorem isOpen_originalEndCoordinateOverlap (a b : IntrinsicBoundary.Point k M × ℝ) :
    IsOpen (originalEndCoordinateOverlap a b) :=
  (chartAt ((Model k × ℝ)) a).continuousOn_symm.isOpen_inter_preimage
    (chartAt ((Model k × ℝ)) a).open_target (chartAt ((Model k × ℝ)) b).open_source

theorem contDiffOn_originalEndCoordinateTransition (a b : IntrinsicBoundary.Point k M × ℝ) :
    ContDiffOn ℝ ∞ ((chartAt ((Model k × ℝ)) b) ∘ (chartAt ((Model k × ℝ)) a).symm)
      (originalEndCoordinateOverlap a b) := by
  intro y hy
  have hs := (contMDiffOn_chart_symm (I := 𝓘(ℝ, (Model k × ℝ))) (x := a) (n := ∞)).contMDiffAt
    ((chartAt ((Model k × ℝ)) a).open_target.mem_nhds hy.1)
  have ht := (contMDiffOn_chart (I := 𝓘(ℝ, (Model k × ℝ))) (x := b) (n := ∞)).contMDiffAt
    ((chartAt ((Model k × ℝ)) b).open_source.mem_nhds hy.2)
  exact (ht.comp y hs).contDiffAt.contDiffWithinAt

/-- The transition's spatial derivative is smooth on the real open overlap,
so parameter endpoints introduce no new derivative extension hypothesis. -/
theorem contDiffOn_originalEndCoordinateTransition_derivative
    (a b : IntrinsicBoundary.Point k M × ℝ) :
    ContDiffOn ℝ ∞
      (fderiv ℝ ((chartAt ((Model k × ℝ)) b) ∘ (chartAt ((Model k × ℝ)) a).symm))
      (originalEndCoordinateOverlap a b) :=
  (contDiffOn_originalEndCoordinateTransition a b).fderiv_of_isOpen
    (isOpen_originalEndCoordinateOverlap a b) (by simp)

/-- Smooth original coframe extensions have a smooth squared transition in
real parameter–spatial coordinates. The spatial derivative is derived from
the original charts; it is not a smoothness hypothesis. -/
theorem contDiffOn_originalEndSquaredTransition
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (a b : IntrinsicBoundary.Point k M × ℝ)
    {U V : Set (ℝ × (Model k × ℝ))}
    {Ca Cb : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] TangentCoordinates n}
    (hCa : ContDiffOn ℝ ∞ Ca U) (hCb : ContDiffOn ℝ ∞ Cb V)
    (hU : U ⊆ univ ×ˢ originalEndCoordinateOverlap a b)
    (hV : ∀ p ∈ U,
      (p.1, chartAt ((Model k × ℝ)) b ((chartAt ((Model k × ℝ)) a).symm p.2)) ∈ V)
    (hCai : ∀ p ∈ U, (Ca p).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Model k × ℝ) =>
      squaredCoframeTransition
        (((Cb (p.1, chartAt ((Model k × ℝ)) b ((chartAt ((Model k × ℝ)) a).symm p.2))).comp
          (fderiv ℝ ((chartAt ((Model k × ℝ)) b) ∘
            (chartAt ((Model k × ℝ)) a).symm) p.2)).comp P.toContinuousLinearMap)
        ((Ca p).comp P.toContinuousLinearMap)) U := by
  let g := (chartAt ((Model k × ℝ)) b) ∘ (chartAt ((Model k × ℝ)) a).symm
  have hg : ContDiffOn ℝ ∞ (fun p : ℝ × (Model k × ℝ) => g p.2) U :=
    (contDiffOn_originalEndCoordinateTransition a b).comp contDiffOn_snd
      (fun _ hp => (hU hp).2)
  have hd : ContDiffOn ℝ ∞ (fun p : ℝ × (Model k × ℝ) => fderiv ℝ g p.2) U :=
    (contDiffOn_originalEndCoordinateTransition_derivative a b).comp contDiffOn_snd
      (fun _ hp => (hU hp).2)
  have hcb := hCb.comp (contDiffOn_fst.prodMk hg) hV
  exact contDiffOn_squaredCoframeTransition
    ((hcb.clm_comp hd).clm_comp contDiffOn_const)
    (hCa.clm_comp contDiffOn_const)
    (fun p hp => (hCai p hp).comp ⟨P, rfl⟩)


end FsFltz.Geometry.IntrinsicCompletionGluing
