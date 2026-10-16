import FsFltz.Geometry.OriginalBundleCompletionMarkingRegularity
import FsFltz.Geometry.ParameterCompleteFlowGerms
import FsFltz.Geometry.PrescribedFamilyCollarGerms

/-!
# Marking germs from ordinary source-field extensions along finite orbits

Source: `geoemtric-part-fsf.tex`, smoothness convention, lines 119–122;
`def:pair`, lines 143–158; `def:chain`, lines 163–199; `g:initial`,
lines 374–384; and `sec:lean`, lines 788–814. The actual source complete
field is transported into the independent fixed source coordinates by
differentiating their slice diffeomorphisms. Smoothness and the ODE of this
transported field follow from the actual source field and complete flow.
Ordinary local smooth field extensions along compact finite source orbits
then produce real flow germs and, with the source compact inclusion, germs
of the actual retained marking on the full original native atlas.

An ordinary smooth family of the actual source primitives supplies these
local field extensions. No marking map germ, pulled Maslov tensor, complete
off-interval flow, or later geometric target assertion is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- The actual source field in independently prescribed source coordinates.
This is the differential of the slice diffeomorphism applied to the source
Liouville field at the inverse image. -/
def completeFieldInCoordinates {d : ℕ} (X : CompleteLiouvilleManifold d)
    (N : SmoothManifold d) (R : X.manifold.SmoothEquiv N) (x : N.Point) : N.Tangent x :=
  mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) R (R.symm x) (X.field (R.symm x))

/-- Slice field smoothness in the fixed coordinates follows from the
actual smooth source field and the smooth tangent map of its diffeomorphism. -/
theorem completeFieldInCoordinates_smooth {d : ℕ} (X : CompleteLiouvilleManifold d)
    (N : SmoothManifold d) (R : X.manifold.SmoothEquiv N) :
    ContMDiff 𝓘(ℝ, Model d) (𝓘(ℝ, Model d)).tangent ∞
      (fun x => (⟨x, completeFieldInCoordinates X N R x⟩ : TangentBundle 𝓘(ℝ, Model d) N.Point)) := by
  have h := (R.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (X.smooth_field.contMDiff_section.comp R.symm.contMDiff)
  convert h using 1
  funext x
  simp only [Function.comp_apply, tangentMap, completeFieldInCoordinates]
  rw [R.apply_symm_apply x]

/-- Differentiating the source-coordinate map transports the actual ODE.
No new equation for the conjugated flow is an input. -/
theorem completeFlowInCoordinates_isMIntegralCurve {d : ℕ} (X : CompleteLiouvilleManifold d)
    (N : SmoothManifold d) (R : X.manifold.SmoothEquiv N) (x : N.Point) :
    IsMIntegralCurve (fun r => R (X.completeFlow.flow r (R.symm x)))
      (completeFieldInCoordinates X N R) := by
  intro r
  have h := ((R.contMDiff.mdifferentiable (by simp))
    (X.completeFlow.flow r (R.symm x))).hasMFDerivAt.comp r
      (X.completeFlow.isMIntegralCurve (R.symm x) r)
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) R (X.completeFlow.flow r (R.symm x))
    (a • X.field (X.completeFlow.flow r (R.symm x))) =
      a • completeFieldInCoordinates X N R (R (X.completeFlow.flow r (R.symm x)))
  rw [map_smul]
  unfold completeFieldInCoordinates
  rw [R.symm_apply_apply]

/-- Ordinary field extensions near finite actual source-orbit segments
produce joint real germs of the actual conjugated complete flows. -/
theorem completeFlowInCoordinates_realGerms_of_local_field_extension
    {d : ℕ} (Z : Parameter → CompleteLiouvilleManifold d) (N : SmoothManifold d)
    (R : ∀ s, (Z s).manifold.SmoothEquiv N) (S : Set Parameter)
    (hlocal : ∀ s ∈ S, ∀ r (x : N.Point),
      ∃ (T : ℝ) (W : ℝ → (y : N.Point) → N.Tangent y) (Ω : Set (ℝ × N.Point)),
        |r| < T ∧ IsOpen Ω ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
          (fun p => (⟨p.2, W p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) N.Point)) Ω ∧
        (∀ v ∈ S, ∀ y, (v.val, y) ∈ Ω →
          W v.val y = completeFieldInCoordinates (Z v) N (R v) y) ∧
        ∀ a ∈ Icc (-T) T, (s.val, R s ((Z s).completeFlow.flow a ((R s).symm x))) ∈ Ω) :
    HasRealSmoothFlowGermsOn N S
      (fun s r y => R s ((Z s).completeFlow.flow r ((R s).symm y))) := by
  intro s hs r x
  obtain ⟨T, W, Ω, hT, hΩ, hW, hext, horbit⟩ := hlocal s hs r x
  exact CollarFlow.exists_parameterCompleteFlow_realGerm S
    (fun v => completeFieldInCoordinates (Z v) N (R v))
    (fun v _ => completeFieldInCoordinates_smooth (Z v) N (R v))
    (fun v a y => R v ((Z v).completeFlow.flow a ((R v).symm y)))
    (fun v _ y => by simp only [Flow.map_zero_apply, (R v).apply_symm_apply])
    (fun v _ y => completeFlowInCoordinates_isMIntegralCurve (Z v) N (R v) y)
    W hΩ hW hext s hs r x T hT horbit

/-- Smoothness of the actual source primitives in the given fixed
coordinates produces all finite-time source-flow germs. The Liouville
equation supplies field regularity, and its real-open native neighborhood
contains each compact orbit segment at every actual interval parameter. -/
theorem completeFlowInCoordinates_realGerms_of_smooth_primitive
    {d : ℕ} (Z : Parameter → CompleteLiouvilleManifold d) (N : SmoothManifold d)
    (R : ∀ s, (Z s).manifold.SmoothEquiv N) (S : Set Parameter)
    (hα : N.IsSmoothIntervalFormFamily
      (fun s => N.pullback (Z s).manifold (R s).symm (Z s).primitive)) :
    HasRealSmoothFlowGermsOn N S
      (fun s r y => R s ((Z s).completeFlow.flow r ((R s).symm y))) := by
  have hfields := CompleteLiouvilleManifold.isSmoothIntervalVectorFieldFamily_pullback
    N Z (fun s => (R s).symm) hα
  change N.IsSmoothIntervalVectorFieldFamily
    (fun s => completeFieldInCoordinates (Z s) N (R s)) at hfields
  obtain ⟨W, hW, hWeq⟩ := hfields
  obtain ⟨Ω, hΩ, hcover, hWnative⟩ := hW.exists_contMDiffOn_neighborhood
  apply completeFlowInCoordinates_realGerms_of_local_field_extension Z N R S
  intro s hs r x
  refine ⟨|r| + 1, W, Ω, by linarith, hΩ, hWnative, ?_, ?_⟩
  · intro v hv y hy
    exact congrFun (hWeq v) y
  · intro a ha
    exact hcover ⟨s.property, mem_univ _⟩

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {Z : Parameter → CompleteLiouvilleManifold d}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

local instance markingFieldProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

namespace OriginalBundleCompletionMarkingData

/-- Direct source-inclusion and ordinary source-field hypotheses produce
the literal retained marking germs on the full interior and signed cylinder.
All source ODE laws and slice field smoothness are derived from the supplied
completed source; the only family-field input is a local real extension near
each finite actual orbit segment. -/
theorem localEquiv_realGerms_of_source_inclusion_and_field_extension
    (O : OriginalBundleCompletionMarkingData L Z) (F : LocalCompletionFamily P c t)
    (N : SmoothManifold d) (R : ∀ s, (Z s).manifold.SmoothEquiv N)
    (hi : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N F.base
      (fun s x => R s (chartValue c.val (O.compact s) s x)))
    (hlocal : ∀ s ∈ F.base, ∀ r (x : N.Point),
      ∃ (T : ℝ) (W : ℝ → (y : N.Point) → N.Tangent y) (Ω : Set (ℝ × N.Point)),
        |r| < T ∧ IsOpen Ω ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
          (fun p => (⟨p.2, W p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) N.Point)) Ω ∧
        (∀ v ∈ F.base, ∀ y, (v.val, y) ∈ Ω →
          W v.val y = completeFieldInCoordinates (Z v) N (R v) y) ∧
        ∀ a ∈ Icc (-T) T, (s.val, R s ((Z s).completeFlow.flow a ((R s).symm x))) ∈ Ω) :
    (∀ s (_hs : s ∈ F.base) (u w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
        (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
        ∃ β : ℝ × Model (k + 1) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) z, z ∈ (chartAt (Model (k + 1)) u).source →
            (v.val, chartAt (Model (k + 1)) u z) ∈ U →
            β (v.val, chartAt (Model (k + 1)) u z) =
              ((O.localEquiv F v hv).trans (R v)) (interiorIn (F.native.patches v) z)) ∧
    (∀ s (_hs : s ∈ F.base) (u : IntrinsicBoundary.Point k M × ℝ)
      (p : Band F.native.width (IntrinsicBoundary.Point k M)),
      endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
      ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
        (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ U ∧
        ∃ β : ℝ × (Model k × ℝ) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) (q : Band F.native.width (IntrinsicBoundary.Point k M)),
            endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
            (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U →
            β (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
              ((O.localEquiv F v hv).trans (R v)) (cylinder (F.native.patches v) q)) :=
  O.localEquiv_realGerms_of_source_inclusion_and_flow F N R hi
    (completeFlowInCoordinates_realGerms_of_local_field_extension Z N R F.base hlocal)

/-- Ordinary source primitive-family smoothness and compact inclusion
smoothness give the literal retained marking germs on the entire native
interior and full signed cylinder. Joint flow regularity is proved here,
rather than supplied as a marking or flow-germ premise. -/
theorem localEquiv_realGerms_of_source_inclusion_and_primitive_smooth
    (O : OriginalBundleCompletionMarkingData L Z) (F : LocalCompletionFamily P c t)
    (N : SmoothManifold d) (R : ∀ s, (Z s).manifold.SmoothEquiv N)
    (hi : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N F.base
      (fun s x => R s (chartValue c.val (O.compact s) s x)))
    (hα : N.IsSmoothIntervalFormFamily
      (fun s => N.pullback (Z s).manifold (R s).symm (Z s).primitive)) :
    (∀ s (_hs : s ∈ F.base) (u w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
        (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
        ∃ β : ℝ × Model (k + 1) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) z, z ∈ (chartAt (Model (k + 1)) u).source →
            (v.val, chartAt (Model (k + 1)) u z) ∈ U →
            β (v.val, chartAt (Model (k + 1)) u z) =
              ((O.localEquiv F v hv).trans (R v)) (interiorIn (F.native.patches v) z)) ∧
    (∀ s (_hs : s ∈ F.base) (u : IntrinsicBoundary.Point k M × ℝ)
      (p : Band F.native.width (IntrinsicBoundary.Point k M)),
      endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
      ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
        (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ U ∧
        ∃ β : ℝ × (Model k × ℝ) → N.Point,
          ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model d) ∞ β U ∧
          ∀ v (hv : v ∈ F.base) (q : Band F.native.width (IntrinsicBoundary.Point k M)),
            endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
            (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U →
            β (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
              ((O.localEquiv F v hv).trans (R v)) (cylinder (F.native.patches v) q)) :=
  O.localEquiv_realGerms_of_source_inclusion_and_flow F N R hi
    (completeFlowInCoordinates_realGerms_of_smooth_primitive Z N R F.base hα)

end OriginalBundleCompletionMarkingData

end FsFltz.Geometry.IntrinsicSmoothBundle
