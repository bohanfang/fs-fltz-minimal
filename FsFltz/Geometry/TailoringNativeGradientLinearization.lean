import FsFltz.Geometry.TailoringNormalGeometry

/-!
# The actual metric-gradient field in native critical fiber charts

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1538–1570,
and `lem:stable`, lines 1709–1724. The field is the actual intrinsic
Liouville field in the actual fiber chart; its metric is the same potential's
Hessian pulled back through the constructed logarithmic lift.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz
open Geometry Geometry.SmoothManifold Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

variable {n d : ℕ} {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
  {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
  {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
  {a : N.Point} {x : TangentCoordinates n}

namespace NativeFaceHessianChart

/-- The coordinate expression of the actual primitive-determined field. -/
def coordinateField (_C : NativeFaceHessianChart φ s H q lam N j a x) :
    Model d → Model d :=
  N.vectorInChart a (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))

/-- The actual restricted potential in the fiber chart. -/
def coordinatePotential (_C : NativeFaceHessianChart φ s H q lam N j a x) :
    Model d → ℝ := fun y => φ (j.map ((chartAt (Model d) a).symm y)).1

/-- Covector form of the actual pulled-back radial and angular Hessian metric. -/
def coordinateMetric (C : NativeFaceHessianChart φ s H q lam N j a x)
    (y : Model d) : Model d →L[ℝ] Model d →L[ℝ] ℝ :=
  let D := fderiv ℝ C.lift y
  let Hy := fderiv ℝ (coordinateGradient φ) (C.lift y).1
  let Dr := (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).comp D
  let Da := (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)).comp D
  (∑ i : Fin n, ((ContinuousLinearMap.proj i).comp (Hy.comp Dr)).smulRight
    ((ContinuousLinearMap.proj i).comp Dr)) +
  ∑ i : Fin n, ((ContinuousLinearMap.proj i).comp (Hy.comp Da)).smulRight
    ((ContinuousLinearMap.proj i).comp Da)

@[simp] theorem coordinateMetric_apply
    (C : NativeFaceHessianChart φ s H q lam N j a x) (y : Model d) (v w : Model d) :
    C.coordinateMetric y v w =
      faceHessianMetric (fderiv ℝ (coordinateGradient φ) (C.lift y).1)
        (fderiv ℝ C.lift y v) (fderiv ℝ C.lift y w) := by
  simp [coordinateMetric, faceHessianMetric,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]

theorem coordinatePotential_smooth
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ) :
    ContDiffAt ℝ ∞ C.coordinatePotential (chartAt (Model d) a a) := by
  apply (hφ.contDiffAt.comp _ C.smooth.fst).congr_of_eventuallyEq
  filter_upwards [C.cover] with y hy
  exact (congrArg (fun p : LGSpace n => φ p.1) hy).symm

theorem coordinateMetric_smooth
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ) :
    ContDiffAt ℝ ∞ C.coordinateMetric (chartAt (Model d) a a) := by
  have hD := C.smooth.fderiv_right (m := ∞) (by simp)
  have hHy := ((contDiff_coordinateGradient hφ).contDiffAt.fderiv_right
    (m := ∞) (by simp)).comp _ C.smooth.fst
  have hr := contDiffAt_const.clm_comp hD
    (f := fun y => fderiv ℝ C.lift y)
    (g := fun _ => ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))
  have ha := contDiffAt_const.clm_comp hD
    (f := fun y => fderiv ℝ C.lift y)
    (g := fun _ => ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n))
  exact (ContDiffAt.sum fun i _ =>
    (contDiffAt_const.clm_comp (hHy.clm_comp hr)).smulRight
      (contDiffAt_const.clm_comp hr)).add
    (ContDiffAt.sum fun i _ =>
      (contDiffAt_const.clm_comp (hHy.clm_comp ha)).smulRight
        (contDiffAt_const.clm_comp ha))

/-- The actual cover identity differentiates throughout a neighborhood,
not only at the critical center. -/
theorem eventually_lift_tangent
    (C : NativeFaceHessianChart φ s H q lam N j a x) :
    ∀ᶠ y in 𝓝 (chartAt (Model d) a a),
      (lgCoverTangent (C.lift y)).comp (fderiv ℝ C.lift y) =
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map
          ((chartAt (Model d) a).symm y)).comp (N.inverseChartTangentMap a y) := by
  let c := chartAt (Model d) a
  have ht : ∀ᶠ y in 𝓝 (c a), y ∈ c.target :=
    c.open_target.mem_nhds (c.map_source (mem_chart_source _ _))
  have hcover : (lgCover ∘ C.lift) =ᶠ[𝓝 (c a)] (j.map ∘ c.symm) := C.cover
  have hs₁ : ContDiffAt ℝ 1 C.lift (c a) := C.smooth.of_le (by simp)
  filter_upwards [hcover.eventuallyEq_nhds,
    hs₁.eventually (by simp), ht] with y he hs hy
  have hd := he.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model (2 * n)))
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (lgCover ∘ C.lift) y =
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (j.map ∘ c.symm) y at hd
  rw [mfderiv_comp y ((contMDiff_lgCover n).mdifferentiable (by simp) _)
      (hs.contMDiffAt.mdifferentiableAt (by simp)),
    mfderiv_comp y (j.map.contMDiff.mdifferentiable (by simp) _)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy),
    mfderiv_eq_fderiv] at hd
  exact hd

/-- Smoothness of the actual chart field follows from primitive smoothness
and the actual nondegeneracy, rather than an assigned smooth field. -/
theorem coordinateField_smooth
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ)
    (hnd : ∀ b, N.Nondegenerate
      (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) b) :
    ContDiffAt ℝ ∞ C.coordinateField (chartAt (Model d) a a) := by
  exact (N.isSmoothVectorField_liouvilleVector _
    (N.isSmoothForm_pullback_one _ j.map _ (isSmoothForm_lambdaPotentialForm hφ))
    hnd a).contDiffAt ((chartAt (Model d) a).open_target.mem_nhds
      ((chartAt (Model d) a).map_source (mem_chart_source _ _)))

theorem coordinateMetric_symm
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ)
    (y : Model d) (v w : Model d) :
    C.coordinateMetric y v w = C.coordinateMetric y w v := by
  simp only [coordinateMetric_apply, faceHessianMetric]
  rw [coordinate_hessian_symmetric_at (hφ.differentiable (by simp)) hφ.contDiffAt
    (fderiv ℝ C.lift y v).1 (fderiv ℝ C.lift y w).1,
    coordinate_hessian_symmetric_at (hφ.differentiable (by simp)) hφ.contDiffAt
      (fderiv ℝ C.lift y v).2 (fderiv ℝ C.lift y w).2]

theorem coordinateMetric_pos
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (v : Model d) (hv : v ≠ 0) :
    0 < C.coordinateMetric (chartAt (Model d) a a) v v := by
  rw [coordinateMetric_apply, C.center,
    ← exteriorDerivative_lambdaPotentialForm_metric_eq hφ]
  apply exteriorDerivative_lambdaPotentialForm_complex_pos hφ hc hlower
  intro hz
  exact hv (C.immersion (hz.trans (map_zero _).symm))

end NativeFaceHessianChart

/-- The true full fiber has nondegenerate restricted differential, from
the proved actual tangent image and positive plane pairing. -/
theorem tailoring_fullFiber_nondegenerate
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1}) (b : N.Point) :
    N.Nondegenerate
      (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) b := by
  have hb : tailoringFamily I β 1 (j.map b) = 1 := by
    have hm : j.map b ∈ range j.map := ⟨b, rfl⟩
    rwa [himage] at hm
  apply (lgManifold n).nondegenerate_pullback_of_rankTwo_kernel N j
    (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) b
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map b))
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map b)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map b)))
    (hpi _ hb).ne'
  rw [← (lgManifold n).complexDifferential_ker_eq_real_inf_imag]
  exact tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1 hpi j himage b

namespace NativeFaceHessianChart

set_option maxHeartbeats 800000 in
/-- The actual chart Liouville field is the metric gradient on a genuine
neighborhood. The input plateau germ is an analytic tailoring property;
the covector identity itself is proved from native contraction and kernels. -/
theorem coordinate_gradient
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c₀ : ℝ} (hc : 0 < c₀)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c₀ * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    {N : SmoothManifold (2 * n - 2)} {j : N.SmoothEmbedding (lgManifold n)}
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1) :
    (fun y => C.coordinateMetric y (C.coordinateField y)) =ᶠ[
      𝓝 (chartAt (Model (2 * n - 2)) a a)] fderiv ℝ C.coordinatePotential := by
  let c := chartAt (Model (2 * n - 2)) a
  let μ := N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)
  have ht : ∀ᶠ y in 𝓝 (c a), y ∈ c.target :=
    c.open_target.mem_nhds (c.map_source (mem_chart_source _ _))
  have hcover : (lgCover ∘ C.lift) =ᶠ[𝓝 (c a)] (j.map ∘ c.symm) := C.cover
  have hs₁ : ContDiffAt ℝ 1 C.lift (c a) := C.smooth.of_le (by simp)
  have hg : ∀ᶠ y in 𝓝 (c a), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v (C.lift y).1 = 0 ∨ tailoringCutoff I β v (C.lift y).1 = 1 := by
    have htend := (contMDiff_lgCover n).continuous.continuousAt.comp C.smooth.continuousAt
    have hten : Tendsto (fun y => lgCover (C.lift y)) (𝓝 (c a))
        (𝓝 (lgCover (C.lift (c a)))) := htend.tendsto
    rw [C.center] at hten
    exact hten.eventually hgood
  filter_upwards [C.eventually_lift_tangent, hcover.eventuallyEq_nhds,
    hs₁.eventually (by simp), ht, hg] with y hd he hs hy hgoodY
  let b := c.symm y
  let z := C.lift y
  let D := mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map b
  have hpoint : lgCover z = j.map b := he.eq_of_nhds
  have hb : tailoringFamily I β 1 (j.map b) = 1 := by
    have hm : j.map b ∈ range j.map := ⟨b, rfl⟩
    rwa [himage] at hm
  have hz : tailoringFamily I β 1 (lgCover z) = 1 := hpoint.symm ▸ hb
  have hkernel := tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1 hpi j himage b
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map b)
  have hpush := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection N j
    (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) b hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map b)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map b)))
    (hpi _ hb).ne'
    (hkernel.trans ((lgManifold n).complexDifferential_ker_eq_real_inf_imag _ _))
  have hi : N.inverseChartTangentMap a y (C.coordinateField y) =
      N.liouvilleVector μ b := by
    have h := congrArg (fun L => L (N.liouvilleVector μ b))
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n - 2))) a).symm_comp_deriv
        (c.map_target hy))
    change N.inverseChartTangentMap a (c b) (C.coordinateField y) = _ at h
    rwa [c.right_inv hy] at h
  have hfield : lgCoverTangent z (fderiv ℝ C.lift y (C.coordinateField y)) =
      D (N.liouvilleVector μ b) := by
    have h := congrArg (fun L : Model (2 * n - 2) →L[ℝ] Model (2 * n) =>
      L (C.coordinateField y)) hd
    change lgCoverTangent z (fderiv ℝ C.lift y (C.coordinateField y)) =
      D (N.inverseChartTangentMap a y (C.coordinateField y)) at h
    rwa [hi] at h
  let P : (lgManifold n).Point → Model (2 * n) := fun p =>
    (lgManifold n).rankTwoFiberProjection
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) p
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower p)
      (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) p))
      (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) p))
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) p)
  change D (N.liouvilleVector μ b) = P (j.map b) at hpush
  have hproj : lgCoverTangent z (fderiv ℝ C.lift y (C.coordinateField y)) =
      P (lgCover z) := hfield.trans (hpush.trans (congrArg P hpoint.symm))
  apply ContinuousLinearMap.ext
  intro w
  have htan : fderiv ℝ (fun p => tailoringFamily I β 1 (lgCover p)) z
      (fderiv ℝ C.lift y w) = 0 := by
    rw [fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)]
    have h := congrArg (fun L : Model (2 * n - 2) →L[ℝ] Model (2 * n) => L w) hd
    change lgCoverTangent z (fderiv ℝ C.lift y w) = D (N.inverseChartTangentMap a y w) at h
    rw [ContinuousLinearMap.comp_apply]
    erw [hpoint, h]
    have hm : D (N.inverseChartTangentMap a y w) ∈ D.range := ⟨_, rfl⟩
    rw [hkernel] at hm
    exact hm
  have hgrad := tailoring_good_projectedLiouville_gradient I β z hz hgoodY hφ
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover z))
    (fderiv ℝ C.lift y (C.coordinateField y)) hproj (fderiv ℝ C.lift y w) htan
  rw [exteriorDerivative_lambdaPotentialForm_metric_eq hφ,
    scalarDerivative_potential_lgCover hφ] at hgrad
  rw [coordinateMetric_apply]
  have hp : C.coordinatePotential =ᶠ[𝓝 y] (fun v => φ (C.lift v).1) := by
    filter_upwards [he] with v hv
    exact (congrArg (fun p : LGSpace n => φ p.1) hv).symm
  rw [hp.fderiv_eq]
  have hr := ((ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).hasFDerivAt.comp y
    (hs.differentiableAt (by simp)).hasFDerivAt)
  have hder := (hφ.differentiable (by simp) _).hasFDerivAt.comp y hr
  change HasFDerivAt (fun v => φ (C.lift v).1)
    ((fderiv ℝ φ (C.lift y).1).comp
      ((ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).comp (fderiv ℝ C.lift y))) y at hder
  rw [hder.fderiv]
  exact hgrad

section ActualLinearization

variable (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
  {c₀ : ℝ} (hc : 0 < c₀)
  (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c₀ * ‖v‖ ^ 2 ≤
    inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
  (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
    0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
  {N : SmoothManifold (2 * n - 2)} {j : N.SmoothEmbedding (lgManifold n)}
  (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
  {a : N.Point} {x : TangentCoordinates n}
  (C : NativeFaceHessianChart φ s H q lam N j a x)
  (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
    tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1)

include I β hφ hc hlower hpi himage hgood

/-- The zero is proved from the actual local gradient identity, stationary
potential and positive metric; no field-zero input is needed. -/
theorem coordinateField_zero : C.coordinateField (chartAt (Model (2 * n - 2)) a a) = 0 := by
  have h := congrArg (fun L : Model (2 * n - 2) →L[ℝ] ℝ =>
    L (C.coordinateField (chartAt (Model (2 * n - 2)) a a)))
    (C.coordinate_gradient I β hφ hc hlower hpi himage hgood).eq_of_nhds
  have hs : fderiv ℝ C.coordinatePotential (chartAt (Model (2 * n - 2)) a a) = 0 := C.stationary
  rw [hs, zero_apply] at h
  by_contra hne
  have hp := C.coordinateMetric_pos hφ hc hlower _ hne
  rw [h] at hp
  exact lt_irrefl 0 hp

/-- The derivative here is the derivative of the actual coordinate field
N.vectorInChart, identified with the actual second derivative of φ. -/
theorem coordinate_linearization (v w : Model (2 * n - 2)) :
    C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
      (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) w =
      fderiv ℝ (fderiv ℝ C.coordinatePotential) (chartAt (Model (2 * n - 2)) a a) v w := by
  exact metric_gradient_linearization
    ((C.coordinateMetric_smooth hφ).differentiableAt (by simp))
    ((C.coordinateField_smooth hφ
      (tailoring_fullFiber_nondegenerate I β hφ hc hlower hpi j himage)).differentiableAt (by simp))
    (C.coordinateField_zero I β hφ hc hlower hpi himage hgood)
    (C.coordinate_gradient I β hφ hc hlower hpi himage hgood) v w

/-- Selfadjointness is for the same native field and the actual induced
metric, and follows from the differentiated neighborhood gradient identity. -/
theorem coordinate_linearization_selfadjoint (v w : Model (2 * n - 2)) :
    C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
      (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) w =
    C.coordinateMetric (chartAt (Model (2 * n - 2)) a a) v
      (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) w) := by
  rw [C.coordinate_linearization I β hφ hc hlower hpi himage hgood,
    C.coordinateMetric_symm hφ _ v _,
    C.coordinate_linearization I β hφ hc hlower hpi himage hgood]
  exact (C.coordinatePotential_smooth hφ).isSymmSndFDerivAt (by simp) v w

/-- Positive actual linearization on the actual face conormal normal. -/
theorem coordinate_linearization_pos_on_conormal_normal
    {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ i, H e i * e i)
    (hq : ∀ v, 0 < q v) (hlam : 0 < lam)
    (v : Model (2 * n - 2)) (hv : v ≠ 0)
    (horth : ∀ W ∈ faceConormalTangent s H q,
      faceHessianMetric H (fderiv ℝ C.lift (chartAt (Model (2 * n - 2)) a a) v) W = 0) :
    0 < C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
      (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) v := by
  rw [C.coordinate_linearization I β hφ hc hlower hpi himage hgood]
  exact C.hessian_pos_on_conormal_normal hB hnormal hHsym hH hq hlam v hv horth

/-- The positive normal is measured against the literal differential image
of the actual radial-angular branch in the native ambient manifold. -/
theorem coordinate_linearization_pos_on_actual_branch_normal
    {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1)
    {g : K → RealSpace n} {f : Torus (n - s.card) → Torus n} {b : K}
    (hg : ContDiffAt ℝ ∞ g b)
    (hf : ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f)
    (hfrange : range f = coneTorus (positiveCone s))
    (θ : Torus (n - s.card))
    (hpoint : conormalBranchAmbientMap g f (b, θ) = lgCover x)
    (hfi : Injective (mfderiv (torusModel (n - s.card)) 𝓘(ℝ, Model (2 * n))
      (faceTorusAmbientMap (g b) f) θ))
    (hgrange : range (fderiv ℝ g b) = {X | X ∈ faceRealTangent q ∧
      H X ∈ Submodule.span ℝ (positiveCone s)})
    {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ i, H e i * e i)
    (hq : ∀ v, 0 < q v) (hlam : 0 < lam)
    (v : Model (2 * n - 2)) (hv : v ≠ 0)
    (horth : ∀ W : TangentCoordinates n,
      lgCoverTangent x W ∈
        (mfderiv ((𝓘(ℝ, K)).prod (torusModel (n - s.card))) 𝓘(ℝ, Model (2 * n))
          (conormalBranchAmbientMap g f) (b, θ)).range →
      evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
        (lgCoverTangent x (fderiv ℝ C.lift (chartAt (Model (2 * n - 2)) a a) v))
        (lgCoverTangent x (coordinateComplexStructure n W)) = 0) :
    0 < C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
      (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) v := by
  rw [C.coordinate_linearization I β hφ hc hlower hpi himage hgood]
  exact C.hessian_pos_on_actual_branch_normal I hs hsne hsproper hφ hHφ
    hg hf hfrange θ hpoint hfi hgrange hB hnormal hHsym hH hq hlam v hv horth

end ActualLinearization

end NativeFaceHessianChart

/-- A uniform threshold supplies all the native metric-gradient data at
every actual critical Hessian chart, including every point on each
constructed critical face torus. The plateau neighborhood, field zero,
smoothness and linearization identity are conclusions, not inputs. -/
theorem IsStronglyCompatibleEndPotential.exists_uniform_native_gradient_linearization
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd)
    {φ : RealSpace n → ℝ} {c U a₀ : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (ha₀ : 0 < a₀) (hEndLower : ∀ u, a₀ * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ (a : N.Point) (x : TangentCoordinates n) (s : Finset (Lattice n))
        (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (lam : ℝ),
      ∀ C : NativeFaceHessianChart φ s H q lam N j a x,
        ContDiffAt ℝ ∞ C.coordinateField (chartAt (Model (2 * n - 2)) a a) ∧
        C.coordinateField (chartAt (Model (2 * n - 2)) a a) = 0 ∧
        ((fun y => C.coordinateMetric y (C.coordinateField y)) =ᶠ[
          𝓝 (chartAt (Model (2 * n - 2)) a a)] fderiv ℝ C.coordinatePotential) ∧
        (∀ v w, C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
          (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) w =
          fderiv ℝ (fderiv ℝ C.coordinatePotential) (chartAt (Model (2 * n - 2)) a a) v w) ∧
        (∀ v w, C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
          (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) w =
          C.coordinateMetric (chartAt (Model (2 * n - 2)) a a) v
            (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) w)) := by
  classical
  obtain ⟨Bh, hBh, hhol⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_holomorphic
    I hφ hc hU hlower hupper hStrong ha₀ hEndLower hEnd
  obtain ⟨_, _, _, _, Bp, _, hplane⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨max Bh Bp, hBh.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage a x s H q lam C
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hplane β ((le_max_right _ _).trans hβ) 1 (by simp) y _).2.2 (by simp [hy])
  obtain ⟨s', _, _, _, _, O, hO, haO, hcut⟩ :=
    hhol β ((le_max_left _ _).trans hβ) N j himage a (Or.inl (C.critical hφ))
  have hpoint : lgCover x = j.map a := by
    have hcover : (lgCover ∘ C.lift) =ᶠ[𝓝 (chartAt (Model (2 * n - 2)) a a)]
      (j.map ∘ (chartAt (Model (2 * n - 2)) a).symm) := C.cover
    have he := hcover.eq_of_nhds
    change lgCover (C.lift (chartAt (Model (2 * n - 2)) a a)) =
      j.map ((chartAt (Model (2 * n - 2)) a).symm (chartAt (Model (2 * n - 2)) a a)) at he
    rw [C.center, (chartAt (Model (2 * n - 2)) a).left_inv (mem_chart_source _ _)] at he
    exact he
  have hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1 := by
    have hnear : ∀ᶠ p in 𝓝 (j.map a), p ∈ O := hO.mem_nhds haO
    rw [← hpoint] at hnear
    filter_upwards [hnear] with p hp v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inr (hcut p hp).1
    · rw [(hcut p hp).2.1 v hv]
      split_ifs <;> simp
  exact ⟨C.coordinateField_smooth hφ
      (tailoring_fullFiber_nondegenerate I β hφ hc hlower hpi j himage),
    C.coordinateField_zero I β hφ hc hlower hpi himage hgood,
    C.coordinate_gradient I β hφ hc hlower hpi himage hgood,
    C.coordinate_linearization I β hφ hc hlower hpi himage hgood,
    C.coordinate_linearization_selfadjoint I β hφ hc hlower hpi himage hgood⟩

end FsFltz
