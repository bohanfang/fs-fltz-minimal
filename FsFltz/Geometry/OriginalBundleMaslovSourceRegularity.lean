import FsFltz.Geometry.OriginalBundleMaslovSourceGerms
import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovSmoothDescent
import FsFltz.Geometry.NativeCanonicalSectionCoordinateBridge
import FsFltz.Geometry.MaslovFamilyCoordinatePullback

/-!
# Source smoothness through literal original marking maps

Source: `geoemtric-part-fsf.tex`, smooth extension (119–122), `def:chain`
(163–199), `def:maslov` (212–244), and `sec:lean` (788–814).
The reference ambient has a fixed underlying smooth manifold and a varying
symplectic family. Real-open germs of actual marking maps, independently of
the section, transport its field and full tensor into original charts.
No coframe or scalar regularity is assumed. A general varying completed
source still requires a smooth local presentation and its actual map germs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry

/-- Differentiate a literal target-map germ after composing with the
original spatial chart. This retains the actual inclusion derivative. -/
theorem mfderiv_markingMapGerm
    {F V W X Y : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace X] [ChartedSpace V X]
    [TopologicalSpace Y] [ChartedSpace W Y]
    {n : ℕ} (N : SmoothManifold (2 * n))
    (s : Parameter) (χ : X → F) (j : X → Y)
    (e : Diffeomorph 𝓘(ℝ, W) 𝓘(ℝ, Model (2 * n)) Y N.Point ∞)
    (A : Set X) (hA : IsOpen A) (z : X) (hz : z ∈ A)
    (U : Set (ℝ × F)) (hU : IsOpen U)
    (β : ℝ × F → N.Point)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × F) 𝓘(ℝ, Model (2 * n)) ∞ β U)
    (hp : (s.val, χ z) ∈ U)
    (hχ : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, F) χ z)
    (hj : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) j z)
    (hχi : (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).IsInvertible)
    (heq : ∀ x ∈ A, (s.val, χ x) ∈ U → β (s.val, χ x) = e (j x))
    (a : N.Point) (ha : e (j z) ∈ (chartAt (Model (2 * n)) a).source) :
    fderiv ℝ (fun y => chartAt (Model (2 * n)) a (β (s.val, y))) (χ z) =
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (chartAt (Model (2 * n)) a) (e (j z))).comp
        ((mfderiv 𝓘(ℝ, W) 𝓘(ℝ, Model (2 * n)) e (j z)).comp
          ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z).comp
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse)) := by
  have hinput : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ × F) ∞ (fun y => (s.val, y)) (χ z) :=
    (show ContDiff ℝ ∞ (fun y : F => (s.val, y)) from
      contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  have hβs : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, Model (2 * n))
      (fun y => β (s.val, y)) (χ z) :=
    ((hβ.contMDiffAt (hU.mem_nhds hp)).comp (χ z)
      hinput).mdifferentiableAt (by simp)
  have hcenter := heq z hz hp
  have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt ha
  have hcs : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, Model (2 * n))
      (fun y => chartAt (Model (2 * n)) a (β (s.val, y))) (χ z) := by
    rw [← hcenter] at hc
    apply (hc.comp (χ z) hβs)
  have hnear : ∀ᶠ x in 𝓝 z, x ∈ A ∧ (s.val, χ x) ∈ U :=
    Filter.Eventually.and (hA.mem_nhds hz)
      ((continuousAt_const.prodMk hχ.continuousAt).preimage_mem_nhds (hU.mem_nhds hp))
  have he : (fun x => chartAt (Model (2 * n)) a (β (s.val, χ x))) =ᶠ[𝓝 z]
      (chartAt (Model (2 * n)) a ∘ e ∘ j) := by
    filter_upwards [hnear] with x hx
    rw [heq x hx.1 hx.2]
    rfl
  have hd := he.mfderiv_eq (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, Model (2 * n)))
  rw [mfderiv_comp z hc ((e.mdifferentiable (by simp)).mdifferentiableAt.comp z hj),
    mfderiv_comp z (e.mdifferentiable (by simp)).mdifferentiableAt hj] at hd
  have hl := mfderiv_comp z hcs hχ
  simp only [Function.comp_def] at hl hd
  rw [hl, mfderiv_eq_fderiv] at hd
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun D => D ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse v)) hd
  change (fderiv ℝ (fun y => chartAt (Model (2 * n)) a (β (s.val, y))) (χ z))
      ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z)
        ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse v)) =
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (chartAt (Model (2 * n)) a) (e (j z)))
        ((mfderiv 𝓘(ℝ, W) 𝓘(ℝ, Model (2 * n)) e (j z))
          ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z)
            ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse v))) at hv
  change (fderiv ℝ (fun y => chartAt (Model (2 * n)) a (β (s.val, y))) (χ z)) v =
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (chartAt (Model (2 * n)) a) (e (j z)))
        ((mfderiv 𝓘(ℝ, W) 𝓘(ℝ, Model (2 * n)) e (j z))
          ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z)
            ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse v)))
  simpa only [hχi.self_apply_inverse] using hv

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicSmoothBundle.CompletedMaslovDimension

/-- Native tangent coordinates preserve the forward field pullback. -/
theorem nativeField_comparison_pullback {d n : ℕ} (h : d = 2 * n)
    (X : CompleteLiouvilleManifold d) (N : SmoothManifold (2 * n))
    (e : X.manifold.SmoothEquiv N) (J : AlmostComplexField N) (x : X.manifold.Point) :
    nativeField h X (pullbackAlmostComplex (ambient h X).manifold N
      (comparison h X N e) J) x =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) e x).inverse.comp
        ((J (e x)).comp (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) e x)) := by
  subst d
  exact pullbackAlmostComplex_eq_inverseDerivative X.manifold N e J x

/-- Native tangent coordinates preserve every forward tensor slot. -/
theorem nativeTensor_comparison_pullback {d n : ℕ} (h : d = 2 * n)
    (X : CompleteLiouvilleManifold d) (N : SmoothManifold (2 * n))
    (e : X.manifold.SmoothEquiv N) (T : N.Point → SquaredCanonicalTensor n)
    (x : X.manifold.Point) :
    nativeTensor h X (pullbackSquaredTensor (ambient h X).manifold N
      (comparison h X N e) T) x =
      (T (e x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) e x) := by
  subst d
  rfl

end FsFltz.Geometry.IntrinsicSmoothBundle.CompletedMaslovDimension

namespace FsFltz.Geometry

/-- Cancellation of an actual source marking and an actual original
chart differential identifies the pulled field and every tensor slot. -/
theorem coordinate_marking_pullback_cancel {n : ℕ} {F W : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (D : W →L[ℝ] F) (hD : D.IsInvertible)
    (E : W →L[ℝ] Model (2 * n)) (hE : E.IsInvertible)
    (B : Model (2 * n) →L[ℝ] Model (2 * n)) (hB : B.IsInvertible)
    (L : F →L[ℝ] Model (2 * n))
    (hL : L = B.comp (E.comp D.inverse))
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (T : SquaredCanonicalTensor n) :
    L.inverse.comp ((B.comp (J.comp B.inverse)).comp L) =
      D.comp ((E.inverse.comp (J.comp E)).comp D.inverse) ∧
    (T.compContinuousLinearMap (fun _ => B.inverse)).compContinuousLinearMap
      (fun _ => L) =
      (T.compContinuousLinearMap (fun _ => E)).compContinuousLinearMap
        (fun _ => D.inverse) := by
  have hi : L.inverse = D.comp (E.inverse.comp B.inverse) := by
    apply ContinuousLinearMap.inverse_eq
    · rw [hL]
      ext v
      simp only [ContinuousLinearMap.comp_apply, hD.inverse_apply_self,
        hE.self_apply_inverse, hB.self_apply_inverse, ContinuousLinearMap.id_apply]
    · rw [hL]
      ext v
      simp only [ContinuousLinearMap.comp_apply, hB.inverse_apply_self,
        hE.inverse_apply_self, hD.self_apply_inverse, ContinuousLinearMap.id_apply]
  constructor
  · rw [hi, hL]
    ext v
    simp only [ContinuousLinearMap.comp_apply, hB.inverse_apply_self]
  · rw [hL]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.comp_apply, hB.inverse_apply_self]

end FsFltz.Geometry

namespace FsFltz.Geometry

/-- A literal smooth marking germ has the invertible spatial derivative
of its actual slice, and its coefficient pullback agrees in all slots. -/
theorem markingMapGerm_coordinate_pullback
    {F V W X Y : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace X] [ChartedSpace V X]
    [TopologicalSpace Y] [ChartedSpace W Y]
    {n : ℕ} (N : SmoothManifold (2 * n))
    (s : Parameter) (χ : X → F) (j : X → Y)
    (e : Diffeomorph 𝓘(ℝ, W) 𝓘(ℝ, Model (2 * n)) Y N.Point ∞)
    (A : Set X) (hA : IsOpen A) (z : X) (hz : z ∈ A)
    (U : Set (ℝ × F)) (hU : IsOpen U)
    (β : ℝ × F → N.Point)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × F) 𝓘(ℝ, Model (2 * n)) ∞ β U)
    (hp : (s.val, χ z) ∈ U)
    (hχ : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, F) χ z)
    (hj : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) j z)
    (hχi : (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).IsInvertible)
    (hji : (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z).IsInvertible)
    (heq : ∀ x ∈ A, (s.val, χ x) ∈ U → β (s.val, χ x) = e (j x))
    (a : N.Point) (ha : e (j z) ∈ (chartAt (Model (2 * n)) a).source)
    (J : ℝ → AlmostComplexField N) (T : ℝ → N.Point → SquaredCanonicalTensor n) :
    let D := (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).comp
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z).inverse
    let E := mfderiv 𝓘(ℝ, W) 𝓘(ℝ, Model (2 * n)) e (j z)
    let φ := fun q : ℝ × F => chartAt (Model (2 * n)) a (β q)
    (coordinateSpatialDerivative φ (s.val, χ z)).IsInvertible ∧
    coordinatePullbackAlmostComplex N a J φ (s.val, χ z) =
      D.comp ((E.inverse.comp ((J s.val (e (j z))).comp E)).comp D.inverse) ∧
    coordinatePullbackSquaredTensor N a T φ (s.val, χ z) =
      ((T s.val (e (j z))).compContinuousLinearMap (fun _ => E)).compContinuousLinearMap
        (fun _ => D.inverse) := by
  dsimp only
  let D : W →L[ℝ] F := (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).comp
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z).inverse
  let E : W →L[ℝ] Model (2 * n) := mfderiv 𝓘(ℝ, W) 𝓘(ℝ, Model (2 * n)) e (j z)
  let B : Model (2 * n) →L[ℝ] Model (2 * n) := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
    (chartAt (Model (2 * n)) a) (e (j z))
  let φ := fun q : ℝ × F => chartAt (Model (2 * n)) a (β q)
  have hD : D.IsInvertible := hχi.comp hji.inverse
  have hE : E.IsInvertible := e.isInvertible_mfderiv (by simp)
  have hB : B.IsInvertible := chartTangentMap_isInvertible N a (e (j z)) ha
  have hDi : D.inverse = (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z).comp
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse := by
    apply ContinuousLinearMap.inverse_eq
    · apply ContinuousLinearMap.ext
      intro v
      change (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z)
        ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z).inverse
          ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z)
            ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse v))) = v
      rw [hji.inverse_apply_self, hχi.self_apply_inverse]
    · apply ContinuousLinearMap.ext
      intro v
      change (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z)
        ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z).inverse
          ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) χ z)
            ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) j z).inverse v))) = v
      rw [hχi.inverse_apply_self, hji.self_apply_inverse]
  have hL : coordinateSpatialDerivative φ (s.val, χ z) = B.comp (E.comp D.inverse) := by
    rw [coordinateSpatialDerivative, hDi]
    exact mfderiv_markingMapGerm N s χ j e A hA z hz U hU β hβ hp hχ hj hχi heq a ha
  have hcenter := heq z hz hp
  let c := chartAt (Model (2 * n)) a
  have hBi : mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) c.symm
      (c (e (j z))) = B.inverse := by
    apply Eq.symm
    apply ContinuousLinearMap.inverse_eq
    · have h := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).comp_symm_deriv
        (c.map_source ha)
      rwa [c.left_inv ha] at h
    · exact (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).symm_comp_deriv ha
  have hJ : almostComplexInChart N a (J s.val) (φ (s.val, χ z)) =
      B.comp ((J s.val (e (j z))).comp B.inverse) := by
    dsimp only [φ, almostComplexInChart]
    change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) c
      (c.symm (c (β (s.val, χ z))))).comp
      ((J s.val (c.symm (c (β (s.val, χ z))))).comp
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) c.symm
          (c (β (s.val, χ z))))) = _
    rw [hcenter, c.left_inv ha, hBi]
  have hT : squaredTensorInChart N a (T s.val) (φ (s.val, χ z)) =
      (T s.val (e (j z))).compContinuousLinearMap (fun _ => B.inverse) := by
    dsimp only [φ, squaredTensorInChart]
    change (T s.val (c.symm (c (β (s.val, χ z))))).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) c.symm
        (c (β (s.val, χ z)))) = _
    rw [hcenter, c.left_inv ha, hBi]
  refine ⟨?_, ?_, ?_⟩
  · rw [hL]
    exact hB.comp (hE.comp hD.inverse)
  · change (coordinateSpatialDerivative φ _).inverse.comp
      ((almostComplexInChart N a (J s.val) (φ _)).comp (coordinateSpatialDerivative φ _)) = _
    rw [hJ]
    exact (coordinate_marking_pullback_cancel D hD E hE B hB _ hL
      (J s.val (e (j z))) (T s.val (e (j z)))).1
  · change (squaredTensorInChart N a (T s.val) (φ _)).compContinuousLinearMap
      (fun _ => coordinateSpatialDerivative φ _) = _
    rw [hT]
    exact (coordinate_marking_pullback_cancel D hD E hE B hB _ hL
      (J s.val (e (j z))) (T s.val (e (j z)))).2

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

local instance sourceRegularityProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance sourceRegularityProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)
  (N : SmoothManifold (2 * n)) (η : ℝ → N.Form 2) (f : MaslovFamily N η)
  (e : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base),
    ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient.manifold.SmoothEquiv N)
  (hJ : ∀ c t ht s hs, S.J c t ht s hs =
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold N
      (CompletedMaslovDimension.comparison hdim
        ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient N (e c t ht s hs))
      (f.J s.val))
  (hT : ∀ c t ht s hs, S.tensor c t ht s hs =
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold N
      (CompletedMaslovDimension.comparison hdim
        ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient N (e c t ht s hs))
      (f.tensor s.val))
  (hmi : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u w : IntrinsicInterior.Point k M),
    w ∈ (chartAt (Model (k + 1)) u).source →
    ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
      (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
      ∃ β : ℝ × Model (k + 1) → N.Point,
        ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ β U ∧
        ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
          (z : IntrinsicInterior.Point k M),
          z ∈ (chartAt (Model (k + 1)) u).source →
          (v.val, chartAt (Model (k + 1)) u z) ∈ U →
          β (v.val, chartAt (Model (k + 1)) u z) =
            e c t ht v hv (interiorIn ((L.localCompletionFamily c t ht).native.patches v) z))
  (hme : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (p : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
    endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
    ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
      (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ U ∧
      ∃ β : ℝ × (Model k × ℝ) → N.Point,
        ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model (2 * n)) ∞ β U ∧
        ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
          (q : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
          endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
          (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U →
          β (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
            e c t ht v hv (cylinder ((L.localCompletionFamily c t ht).native.patches v) q))

include hJ hT hmi hme in
/-- Joint source smoothness and ordinary real marking-map germs produce
all retained original field/full-tensor germs. Only the original retained
parameters carry the identification with the prescribed source section. -/
theorem tensorGerms_of_markingMapGerms : OriginalLocalCompletionMaslovTensorGerms S := by
  constructor
  · intro c t ht s hs u w hw
    let F := L.localCompletionFamily c t ht
    let := completionChartedSpace F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ := hmi c t ht s hs u w hw
    let a := β (s.val, chartAt (Model (k + 1)) u w)
    let C := chartAt (Model (2 * n)) a
    let W := U ∩ β ⁻¹' C.source
    have hW : IsOpen W := hβ.continuousOn.isOpen_inter_preimage hU C.open_source
    have hpW : (s.val, chartAt (Model (k + 1)) u w) ∈ W :=
      ⟨hpU, mem_chart_source _ a⟩
    let φ := fun z : ℝ × Model (k + 1) => C (β z)
    have hφ : ContDiffOn ℝ ∞ φ W :=
      ((contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := a)).comp
        (hβ.mono inter_subset_left) inter_subset_right).contDiffOn
    have hχ := (mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u).mdifferentiableAt hw
    have hχi := chartTangentMap_isInvertible (IntrinsicInterior.smoothManifold k M) u w hw
    have hj := (contMDiff_completionInterior F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
      (F.native.inverse s) (F.native.zero s)).mdifferentiableAt (by simp) (x := w)
    have hji := isInvertible_mfderiv_completionInterior F.native.width_pos
      (F.native.collar s) (F.native.embedding s) (F.native.smooth s)
      (F.native.boundary s) (F.native.inverse s) (F.native.zero s) w
    have hm := markingMapGerm_coordinate_pullback N s (chartAt (Model (k + 1)) u)
      (interiorIn (F.native.patches s)) (e c t ht s hs)
      (chartAt (Model (k + 1)) u).source (chartAt (Model (k + 1)) u).open_source
      w hw U hU β hβ hpU hχ hj hχi hji (heq s hs) a
      (by exact (heq s hs w hw hpU).symm ▸ mem_chart_source _ a) f.J f.tensor
    obtain ⟨V, hV, hpV, hVW, htarget, hK, hT'⟩ := f.exists_coordinatePullback_regularNeighborhood
      a φ hW hφ (s, chartAt (Model (k + 1)) u w) hpW
      (C.map_source (mem_chart_source _ a)) hm.1
    refine ⟨V, hV, hpV, coordinatePullbackAlmostComplex N a f.J φ, hK,
      coordinatePullbackSquaredTensor N a f.tensor φ, hT', ?_⟩
    intro v hv z hz hzV
    have hzU := (hVW hzV).1
    have hzC : e c t ht v hv (interiorIn (F.native.patches v) z) ∈ C.source := by
      rw [← heq v hv z hz hzU]
      exact (hVW hzV).2
    let := completionChartedSpace F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.boundary v) (F.native.zero v)
    have hjz := (contMDiff_completionInterior F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
      (F.native.inverse v) (F.native.zero v)).mdifferentiableAt (by simp) (x := z)
    have hmz := markingMapGerm_coordinate_pullback N v (chartAt (Model (k + 1)) u)
      (interiorIn (F.native.patches v)) (e c t ht v hv)
      (chartAt (Model (k + 1)) u).source (chartAt (Model (k + 1)) u).open_source
      z hz U hU β hβ hzU
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u).mdifferentiableAt hz) hjz
      (chartTangentMap_isInvertible (IntrinsicInterior.smoothManifold k M) u z hz)
      (isInvertible_mfderiv_completionInterior F.native.width_pos (F.native.collar v)
        (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
        (F.native.inverse v) (F.native.zero v) z) (heq v hv) a hzC f.J f.tensor
    have hnJ := CompletedMaslovDimension.nativeField_comparison_pullback hdim
      (F.sliceCompletion L v).ambient N (e c t ht v hv) (f.J v.val)
      (interiorIn (F.native.patches v) z)
    have hnT := CompletedMaslovDimension.nativeTensor_comparison_pullback hdim
      (F.sliceCompletion L v).ambient N (e c t ht v hv) (f.tensor v.val)
      (interiorIn (F.native.patches v) z)
    rw [← hJ c t ht v hv] at hnJ
    rw [← hT c t ht v hv] at hnT
    change S.nativeJ c t ht v hv (interiorIn (F.native.patches v) z) = _ at hnJ
    change S.nativeTensor c t ht v hv (interiorIn (F.native.patches v) z) = _ at hnT
    dsimp only [LocalCompletionFamily.interiorMaslovCoordinateDifferential]
    rw [hnJ, hnT]
    exact ⟨hmz.2.1, hmz.2.2⟩
  · intro c t ht s hs u p hp
    let F := L.localCompletionFamily c t ht
    let := completionChartedSpace F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
    let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) F.native.width
    let χ := chartAt (Model k × ℝ) u ∘ endBandCoordinates (δ := F.native.width)
    let A := endBandCoordinates (δ := F.native.width) ⁻¹' (chartAt (Model k × ℝ) u).source
    have hA : IsOpen A := (chartAt (Model k × ℝ) u).open_source.preimage
      contMDiff_endBandCoordinates.continuous
    have hχdata (q : Band F.native.width (IntrinsicBoundary.Point k M))
        (hq : endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source) :
        MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q ∧
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q).IsInvertible := by
      have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u).mdifferentiableAt hq
      have hd := contMDiff_endBandCoordinates.mdifferentiableAt (by simp) (x := q)
      have hci : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
          (chartAt (Model k × ℝ) u) (endBandCoordinates q)).IsInvertible := by
        have hm := mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u
        apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hm.symm_comp_deriv hq)
        have h := hm.comp_symm_deriv ((chartAt (Model k × ℝ) u).map_source hq)
        rwa [(chartAt (Model k × ℝ) u).left_inv hq] at h
      refine ⟨hc.comp q hd, ?_⟩
      dsimp only [χ]
      rw [mfderiv_comp q hc hd]
      exact hci.comp (isInvertible_mfderiv_endBandCoordinates q)
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ := hme c t ht s hs u p hp
    let a := β (s.val, χ p)
    let C := chartAt (Model (2 * n)) a
    let W := U ∩ β ⁻¹' C.source
    have hW : IsOpen W := hβ.continuousOn.isOpen_inter_preimage hU C.open_source
    have hpW : (s.val, χ p) ∈ W := ⟨hpU, mem_chart_source _ a⟩
    let φ := fun z : ℝ × (Model k × ℝ) => C (β z)
    have hφ : ContDiffOn ℝ ∞ φ W :=
      ((contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := a)).comp
        (hβ.mono inter_subset_left) inter_subset_right).contDiffOn
    have hj := (contMDiff_cylinder F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
      (F.native.inverse s) (F.native.zero s)).mdifferentiableAt (by simp) (x := p)
    have hji := isInvertible_mfderiv_completionCylinder F.native.width_pos
      (F.native.collar s) (F.native.embedding s) (F.native.smooth s)
      (F.native.boundary s) (F.native.inverse s) (F.native.zero s) p
    have hm := markingMapGerm_coordinate_pullback N s χ
      (cylinder (F.native.patches s)) (e c t ht s hs) A hA p hp U hU β hβ hpU
      (hχdata p hp).1 hj (hχdata p hp).2 hji (heq s hs) a
      (by exact (heq s hs p hp hpU).symm ▸ mem_chart_source _ a) f.J f.tensor
    obtain ⟨V, hV, hpV, hVW, htarget, hK, hT'⟩ := f.exists_coordinatePullback_regularNeighborhood
      a φ hW hφ (s, χ p) hpW (C.map_source (mem_chart_source _ a)) hm.1
    refine ⟨V, hV, hpV, coordinatePullbackAlmostComplex N a f.J φ, hK,
      coordinatePullbackSquaredTensor N a f.tensor φ, hT', ?_⟩
    intro v hv q hq hqV
    have hqU := (hVW hqV).1
    have hqC : e c t ht v hv (cylinder (F.native.patches v) q) ∈ C.source := by
      exact (heq v hv q hq hqU).symm ▸ (hVW hqV).2
    let := completionChartedSpace F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.boundary v) (F.native.zero v)
    have hjq := (contMDiff_cylinder F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
      (F.native.inverse v) (F.native.zero v)).mdifferentiableAt (by simp) (x := q)
    have hmz := markingMapGerm_coordinate_pullback N v χ
      (cylinder (F.native.patches v)) (e c t ht v hv) A hA q hq U hU β hβ hqU
      (hχdata q hq).1 hjq (hχdata q hq).2
      (isInvertible_mfderiv_completionCylinder F.native.width_pos (F.native.collar v)
        (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
        (F.native.inverse v) (F.native.zero v) q) (heq v hv) a hqC f.J f.tensor
    have hdχ : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q =
        (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
          (chartAt (Model k × ℝ) u) (endBandCoordinates q)).comp
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates q) :=
      mfderiv_comp q
        ((mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u).mdifferentiableAt hq)
        (contMDiff_endBandCoordinates.mdifferentiableAt (by simp))
    have hnJ := CompletedMaslovDimension.nativeField_comparison_pullback hdim
      (F.sliceCompletion L v).ambient N (e c t ht v hv) (f.J v.val)
      (cylinder (F.native.patches v) q)
    have hnT := CompletedMaslovDimension.nativeTensor_comparison_pullback hdim
      (F.sliceCompletion L v).ambient N (e c t ht v hv) (f.tensor v.val)
      (cylinder (F.native.patches v) q)
    rw [← hJ c t ht v hv] at hnJ
    rw [← hT c t ht v hv] at hnT
    change S.nativeJ c t ht v hv (cylinder (F.native.patches v) q) = _ at hnJ
    change S.nativeTensor c t ht v hv (cylinder (F.native.patches v) q) = _ at hnT
    have hD : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
          (cylinder (F.native.patches v)) q).inverse =
        F.endMaslovCoordinateDifferential v u q := by
      rw [hdχ]
      rfl
    dsimp only
    rw [hnJ, hnT]
    dsimp only at hmz
    rw [hD] at hmz
    exact ⟨hmz.2.1, hmz.2.2⟩

end OriginalLocalCompletionMaslovData
end FsFltz.Geometry.IntrinsicSmoothBundle
