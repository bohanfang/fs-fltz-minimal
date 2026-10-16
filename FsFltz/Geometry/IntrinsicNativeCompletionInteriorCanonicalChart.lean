import FsFltz.Geometry.IntrinsicNativeCompletionInteriorGradingDerivative
import FsFltz.Geometry.NativeCoordinateCanonicalSection

/-!
# Canonical-square coordinates on the original completed interior

Source: `geoemtric-part-fsf.tex`, smooth extension convention, lines 119–122;
`def:maslov`, lines 212–232; and `sec:lean`, lines 788–814. The original
interior inclusion and its actual differential define the spatial canonical
coordinates. On overlap the inclusion differential cancels, leaving the
literal derivative of the two original interior charts. Thus canonical
coframe coordinates on the original interval base have the prescribed
spatial transition, without a supplied coordinate differential.

This module constructs the interior chart foundation. The full original
vertical atlas, its native section extraction, and the end charts are separate
obligations; the geometric theorem is not asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The actual differential of an original native interior chart. -/
def originalInteriorChartDifferential (a w : IntrinsicInterior.Point k M) :
    Model (k + 1) →L[ℝ] Model (k + 1) :=
  mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    (chartAt (Model (k + 1)) a) w

theorem isInvertible_originalInteriorChartDifferential
    (a w : IntrinsicInterior.Point k M)
    (hw : w ∈ (chartAt (Model (k + 1)) a).source) :
    (originalInteriorChartDifferential a w).IsInvertible := by
  let A := mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) a
  apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (A.symm_comp_deriv hw)
  have h := A.comp_symm_deriv ((chartAt (Model (k + 1)) a).map_source hw)
  rwa [(chartAt (Model (k + 1)) a).left_inv hw] at h

/-- The inverse chart's derivative is the inverse actual chart differential. -/
theorem mfderiv_originalInteriorChart_symm
    (a w : IntrinsicInterior.Point k M)
    (hw : w ∈ (chartAt (Model (k + 1)) a).source) :
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (chartAt (Model (k + 1)) a).symm (chartAt (Model (k + 1)) a w) =
      (originalInteriorChartDifferential a w).inverse := by
  have hi := isInvertible_originalInteriorChartDifferential a w hw
  have h := (mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) a).symm_comp_deriv hw
  change (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    (chartAt (Model (k + 1)) a).symm (chartAt (Model (k + 1)) a w)).comp
      (originalInteriorChartDifferential a w) = ContinuousLinearMap.id ℝ (Model (k + 1)) at h
  ext v
  have he := congrArg (fun L : Model (k + 1) →L[ℝ] Model (k + 1) =>
    L ((originalInteriorChartDifferential a w).inverse v)) h
  change (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    (chartAt (Model (k + 1)) a).symm (chartAt (Model (k + 1)) a w))
      ((originalInteriorChartDifferential a w) ((originalInteriorChartDifferential a w).inverse v)) =
        (originalInteriorChartDifferential a w).inverse v at he
  rw [hi.self_apply_inverse] at he
  exact he

/-- Chart transition differentials come from the literal transition map. -/
theorem fderiv_originalInteriorChart_transition
    (a b w : IntrinsicInterior.Point k M)
    (ha : w ∈ (chartAt (Model (k + 1)) a).source)
    (hb : w ∈ (chartAt (Model (k + 1)) b).source) :
    fderiv ℝ ((chartAt (Model (k + 1)) b) ∘ (chartAt (Model (k + 1)) a).symm)
      (chartAt (Model (k + 1)) a w) =
      (originalInteriorChartDifferential b w).comp
        (originalInteriorChartDifferential a w).inverse := by
  rw [← mfderiv_eq_fderiv]
  have hs := (mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) a).symm
    |>.mdifferentiableAt ((chartAt (Model (k + 1)) a).map_source ha)
  have ht := (mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) b).mdifferentiableAt hb
  have h := mfderiv_comp (chartAt (Model (k + 1)) a w)
    (f := (chartAt (Model (k + 1)) a).symm) (g := chartAt (Model (k + 1)) b)
    (by simpa only [(chartAt (Model (k + 1)) a).left_inv ha] using ht) hs
  rw [(chartAt (Model (k + 1)) a).left_inv ha,
    mfderiv_originalInteriorChart_symm a w ha] at h
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

/-- Canonical coordinates use the actual original inclusion differential;
the spatial model is the native completion tangent, with no time slot. -/
def originalInteriorCanonicalDifferential (a w : IntrinsicInterior.Point k M) :
    Model (k + 1) →L[ℝ] Model (k + 1) :=
  letI := completionChartedSpace hδ C hemb hboundary hzero
  (originalInteriorChartDifferential a w).comp
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) w).inverse

include hC hinv in
theorem isInvertible_originalInteriorCanonicalDifferential
    (a w : IntrinsicInterior.Point k M)
    (hw : w ∈ (chartAt (Model (k + 1)) a).source) :
    (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a w).IsInvertible :=
  (isInvertible_originalInteriorChartDifferential a w hw).comp
    (isInvertible_mfderiv_completionInterior hδ C hemb hC hboundary hinv hzero w).inverse

include hC hinv in
/-- The completion inclusion cancels on overlaps. The remaining map is
the literal original spatial chart derivative, including at time endpoints. -/
theorem originalInteriorCanonicalDifferential_transition
    (a b w : IntrinsicInterior.Point k M)
    (ha : w ∈ (chartAt (Model (k + 1)) a).source)
    (hb : w ∈ (chartAt (Model (k + 1)) b).source) :
    (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero b w).comp
      (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a w).inverse =
    fderiv ℝ ((chartAt (Model (k + 1)) b) ∘ (chartAt (Model (k + 1)) a).symm)
      (chartAt (Model (k + 1)) a w) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  have hi := isInvertible_mfderiv_completionInterior hδ C hemb hC hboundary hinv hzero w
  have haI := isInvertible_originalInteriorChartDifferential a w ha
  rw [fderiv_originalInteriorChart_transition a b w ha hb]
  simp only [originalInteriorCanonicalDifferential]
  rw [haI.inverse_comp_of_left, hi.inverse_inverse]
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (originalInteriorChartDifferential b w)
    (hi.inverse_apply_self ((originalInteriorChartDifferential a w).inverse v))

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry

/-- A common invertible change of real tangent coordinates cancels from the
determinant-square transition. This follows from actual tensor evaluation. -/
theorem squaredCoframeTransition_comp {n : ℕ}
    (C D : Model (2 * n) →L[ℝ] TangentCoordinates n)
    (A : Model (2 * n) →L[ℝ] Model (2 * n)) (hA : A.IsInvertible) :
    squaredCoframeTransition (C.comp A) (D.comp A) = squaredCoframeTransition C D := by
  have hgen : coframeSquaredGenerator (C.comp A) =
      (coframeSquaredGenerator C).compContinuousLinearMap (fun _ => A) := by
    ext v
    rfl
  rw [squaredCoframeTransition, hgen, squaredCoframeCoefficient_comp D A hA]
  rfl

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
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

include hC hinv in
/-- The original native canonical-square transition is calculated using
the actual spatial transition derivative. No completion tangent regularity
or representation of that tangent transition is supplied. -/
theorem originalInteriorCanonical_squaredTransition
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (a b w : IntrinsicInterior.Point k M)
    (ha : w ∈ (chartAt (Model (k + 1)) a).source)
    (hb : w ∈ (chartAt (Model (k + 1)) b).source)
    (Ca Cb : Model (k + 1) →L[ℝ] TangentCoordinates n) :
    squaredCoframeTransition
      ((Cb.comp (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero b w)).comp
        P.toContinuousLinearMap)
      ((Ca.comp (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a w)).comp
        P.toContinuousLinearMap) =
    squaredCoframeTransition
      ((Cb.comp (fderiv ℝ ((chartAt (Model (k + 1)) b) ∘
        (chartAt (Model (k + 1)) a).symm) (chartAt (Model (k + 1)) a w))).comp
          P.toContinuousLinearMap)
      (Ca.comp P.toContinuousLinearMap) := by
  let Ha := originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a w
  let Hb := originalInteriorCanonicalDifferential hδ C hemb hboundary hzero b w
  let L := fderiv ℝ ((chartAt (Model (k + 1)) b) ∘
    (chartAt (Model (k + 1)) a).symm) (chartAt (Model (k + 1)) a w)
  have hi : Ha.IsInvertible :=
    isInvertible_originalInteriorCanonicalDifferential hδ C hemb hC hboundary hinv hzero a w ha
  have ht : Hb.comp Ha.inverse = L :=
    originalInteriorCanonicalDifferential_transition hδ C hemb hC hboundary hinv hzero a b w ha hb
  have hHb : Hb = L.comp Ha := by
    rw [← ht]
    apply ContinuousLinearMap.ext
    intro v
    exact (congrArg Hb (hi.inverse_apply_self v)).symm
  let A := P.symm.toContinuousLinearMap.comp (Ha.comp P.toContinuousLinearMap)
  have hAi : A.IsInvertible :=
    (show P.symm.toContinuousLinearMap.IsInvertible from ⟨P.symm, rfl⟩).comp
      (hi.comp ⟨P, rfl⟩)
  have he := squaredCoframeTransition_comp ((Cb.comp L).comp P.toContinuousLinearMap)
    (Ca.comp P.toContinuousLinearMap) A hAi
  change squaredCoframeTransition ((Cb.comp Hb).comp P.toContinuousLinearMap)
    ((Ca.comp Ha).comp P.toContinuousLinearMap) =
    squaredCoframeTransition ((Cb.comp L).comp P.toContinuousLinearMap)
      (Ca.comp P.toContinuousLinearMap)
  rw [hHb]
  convert he using 1
  ·
    congr 1 <;>
    ext v <;>
    simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]

/-- The real spatial overlap of two original interior charts. -/
def originalInteriorCoordinateOverlap (a b : IntrinsicInterior.Point k M) : Set (Model (k + 1)) :=
  (chartAt (Model (k + 1)) a).target ∩
    (chartAt (Model (k + 1)) a).symm ⁻¹' (chartAt (Model (k + 1)) b).source

theorem isOpen_originalInteriorCoordinateOverlap (a b : IntrinsicInterior.Point k M) :
    IsOpen (originalInteriorCoordinateOverlap a b) :=
  (chartAt (Model (k + 1)) a).continuousOn_symm.isOpen_inter_preimage
    (chartAt (Model (k + 1)) a).open_target (chartAt (Model (k + 1)) b).open_source

theorem contDiffOn_originalInteriorCoordinateTransition (a b : IntrinsicInterior.Point k M) :
    ContDiffOn ℝ ∞ ((chartAt (Model (k + 1)) b) ∘ (chartAt (Model (k + 1)) a).symm)
      (originalInteriorCoordinateOverlap a b) := by
  intro y hy
  have hs := (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (k + 1))) (x := a) (n := ∞)).contMDiffAt
    ((chartAt (Model (k + 1)) a).open_target.mem_nhds hy.1)
  have ht := (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := b) (n := ∞)).contMDiffAt
    ((chartAt (Model (k + 1)) b).open_source.mem_nhds hy.2)
  exact (ht.comp y hs).contDiffAt.contDiffWithinAt

/-- The transition's spatial derivative is smooth on the real open overlap,
so parameter endpoints introduce no new derivative extension hypothesis. -/
theorem contDiffOn_originalInteriorCoordinateTransition_derivative
    (a b : IntrinsicInterior.Point k M) :
    ContDiffOn ℝ ∞
      (fderiv ℝ ((chartAt (Model (k + 1)) b) ∘ (chartAt (Model (k + 1)) a).symm))
      (originalInteriorCoordinateOverlap a b) :=
  (contDiffOn_originalInteriorCoordinateTransition a b).fderiv_of_isOpen
    (isOpen_originalInteriorCoordinateOverlap a b) (by simp)

/-- Smooth original coframe extensions have a smooth squared transition in
real parameter–spatial coordinates. The spatial derivative is derived from
the original charts; it is not a smoothness hypothesis. -/
theorem contDiffOn_originalInteriorSquaredTransition
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (a b : IntrinsicInterior.Point k M)
    {U V : Set (ℝ × Model (k + 1))}
    {Ca Cb : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] TangentCoordinates n}
    (hCa : ContDiffOn ℝ ∞ Ca U) (hCb : ContDiffOn ℝ ∞ Cb V)
    (hU : U ⊆ univ ×ˢ originalInteriorCoordinateOverlap a b)
    (hV : ∀ p ∈ U,
      (p.1, chartAt (Model (k + 1)) b ((chartAt (Model (k + 1)) a).symm p.2)) ∈ V)
    (hCai : ∀ p ∈ U, (Ca p).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Model (k + 1) =>
      squaredCoframeTransition
        (((Cb (p.1, chartAt (Model (k + 1)) b ((chartAt (Model (k + 1)) a).symm p.2))).comp
          (fderiv ℝ ((chartAt (Model (k + 1)) b) ∘
            (chartAt (Model (k + 1)) a).symm) p.2)).comp P.toContinuousLinearMap)
        ((Ca p).comp P.toContinuousLinearMap)) U := by
  let g := (chartAt (Model (k + 1)) b) ∘ (chartAt (Model (k + 1)) a).symm
  have hg : ContDiffOn ℝ ∞ (fun p : ℝ × Model (k + 1) => g p.2) U :=
    (contDiffOn_originalInteriorCoordinateTransition a b).comp contDiffOn_snd
      (fun _ hp => (hU hp).2)
  have hd : ContDiffOn ℝ ∞ (fun p : ℝ × Model (k + 1) => fderiv ℝ g p.2) U :=
    (contDiffOn_originalInteriorCoordinateTransition_derivative a b).comp contDiffOn_snd
      (fun _ hp => (hU hp).2)
  have hcb := hCb.comp (contDiffOn_fst.prodMk hg) hV
  exact contDiffOn_squaredCoframeTransition
    ((hcb.clm_comp hd).clm_comp contDiffOn_const)
    (hCa.clm_comp contDiffOn_const)
    (fun p hp => (hCai p hp).comp ⟨P, rfl⟩)

end FsFltz.Geometry.IntrinsicCompletionGluing
