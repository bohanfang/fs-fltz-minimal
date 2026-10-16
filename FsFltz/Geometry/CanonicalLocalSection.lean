import FsFltz.Geometry.CanonicalBundle

/-!
# Actual local canonical sections in overlapping manifold charts

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. A local complex coframe produces a determinant
square on the manifold itself. Its smoothness is proved in every overlapping
chart using the actual differential of the chart transition. No local
section, frame, or transition smoothness certificate is assumed.

The native global canonical-bundle atlas and change-of-compatible-structure
invariance remain separate foundations.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- Smoothness of an actual squared tensor section on an open part of the
manifold is checked in every atlas chart on its preimage. -/
def IsSmoothSquaredTensorSectionOn {n : ℕ} (M : SmoothManifold (2 * n))
    (s : M.Point → SquaredCanonicalTensor n) (U : Set M.Point) : Prop :=
  ∀ b, ContDiffOn ℝ ∞ (squaredTensorInChart M b s)
    ((chartAt (Model (2 * n)) b).target ∩
      (chartAt (Model (2 * n)) b).symm ⁻¹' U)

@[simp] theorem isSmoothSquaredTensorSectionOn_univ_iff {n : ℕ}
    (M : SmoothManifold (2 * n)) (s : M.Point → SquaredCanonicalTensor n) :
    IsSmoothSquaredTensorSectionOn M s univ ↔ IsSmoothSquaredTensorSection M s := by
  simp only [IsSmoothSquaredTensorSectionOn, IsSmoothSquaredTensorSection,
    preimage_univ, inter_univ]

theorem IsSmoothSquaredTensorSection.isSmoothOn {n : ℕ}
    {M : SmoothManifold (2 * n)} {s : M.Point → SquaredCanonicalTensor n}
    (hs : IsSmoothSquaredTensorSection M s) (U : Set M.Point) :
    IsSmoothSquaredTensorSectionOn M s U :=
  fun b => (hs b).mono inter_subset_left

/-- The manifold neighborhood corresponding to an open coordinate domain. -/
def canonicalChartDomain {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (V : Set (Model (2 * n))) : Set M.Point :=
  (chartAt (Model (2 * n)) a).source ∩ (chartAt (Model (2 * n)) a) ⁻¹' V

theorem isOpen_canonicalChartDomain {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) {V : Set (Model (2 * n))} (hV : IsOpen V) :
    IsOpen (canonicalChartDomain M a V) :=
  (chartAt (Model (2 * n)) a).continuousOn.isOpen_inter_preimage
    (chartAt (Model (2 * n)) a).open_source hV

/-- The intrinsic tangent coframe, obtained by composing a coordinate
coframe with the actual chart differential. -/
def localCanonicalCoframe {n : ℕ} (M : SmoothManifold (2 * n)) (a : M.Point)
    (C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (x : M.Point) : Model (2 * n) →L[ℝ] TangentCoordinates n :=
  (C (chartAt (Model (2 * n)) a x)).comp (M.chartTangentMap a x)

/-- The determinant square is an actual tangent tensor on the manifold,
rather than only a coordinate function on one Euclidean chart. -/
def localCanonicalSquaredSection {n : ℕ} (M : SmoothManifold (2 * n)) (a : M.Point)
    (C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n) :
    M.Point → SquaredCanonicalTensor n :=
  fun x => coframeSquaredGenerator (localCanonicalCoframe M a C x)

set_option backward.isDefEq.respectTransparency false in
/-- In every overlapping chart, the actual local section is the determinant
square of the coframe composed with the derivative of the transition map. -/
theorem localCanonicalSquaredSection_inChart {n : ℕ} (M : SmoothManifold (2 * n))
    (a b : M.Point)
    (C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) b).target)
    (hx : (chartAt (Model (2 * n)) b).symm y ∈ (chartAt (Model (2 * n)) a).source) :
    squaredTensorInChart M b (localCanonicalSquaredSection M a C) y =
      coframeSquaredGenerator
        ((C (chartAt (Model (2 * n)) a ((chartAt (Model (2 * n)) b).symm y))).comp
          (fderiv ℝ (chartAt (Model (2 * n)) a ∘
            (chartAt (Model (2 * n)) b).symm) y)) := by
  rw [← mfderiv_eq_fderiv]
  rw [mfderiv_comp y
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt hx)
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).mdifferentiableAt_symm hy)]
  ext v
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual coframe transported to another chart is computed by the
derivative of the chart transition, on its genuine overlap domain. -/
theorem localCanonicalCoframe_inChart {n : ℕ} (M : SmoothManifold (2 * n))
    (a b : M.Point)
    (C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) b).target)
    (hx : (chartAt (Model (2 * n)) b).symm y ∈ (chartAt (Model (2 * n)) a).source) :
    (localCanonicalCoframe M a C ((chartAt (Model (2 * n)) b).symm y)).comp
        (M.inverseChartTangentMap b y) =
      (C (chartAt (Model (2 * n)) a ((chartAt (Model (2 * n)) b).symm y))).comp
        (fderiv ℝ (chartAt (Model (2 * n)) a ∘
          (chartAt (Model (2 * n)) b).symm) y) := by
  rw [← mfderiv_eq_fderiv]
  rw [mfderiv_comp y
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).mdifferentiableAt hx)
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) b).mdifferentiableAt_symm hy)]
  apply ContinuousLinearMap.ext
  intro v
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness in one coordinate domain produces smoothness of the actual
coframe in every overlapping chart; transition derivatives are derived from
the native smooth manifold structure. -/
theorem contDiffOn_localCanonicalCoframe_inChart {n : ℕ}
    (M : SmoothManifold (2 * n)) (a b : M.Point)
    {V : Set (Model (2 * n))} (hV : IsOpen V)
    {C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C V) :
    ContDiffOn ℝ ∞ (fun y =>
      ((localCanonicalCoframe M a C ((chartAt (Model (2 * n)) b).symm y)).comp
        (M.inverseChartTangentMap b y) : Model (2 * n) →L[ℝ] TangentCoordinates n))
      ((chartAt (Model (2 * n)) b).target ∩
        (chartAt (Model (2 * n)) b).symm ⁻¹' canonicalChartDomain M a V) := by
  let c := chartAt (Model (2 * n)) a
  let d := chartAt (Model (2 * n)) b
  let g := c ∘ d.symm
  have hg : ContDiffOn ℝ ∞ g
      (d.target ∩ d.symm ⁻¹' canonicalChartDomain M a V) := by
    intro y hy
    have hA : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ d.symm y :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
        (d.open_target.mem_nhds hy.1)
    have hB : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ c (d.symm y) :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := a)).contMDiffAt
        (c.open_source.mem_nhds hy.2.1)
    exact (hB.comp y hA).contDiffAt.contDiffWithinAt
  have hD : IsOpen (d.target ∩ d.symm ⁻¹' canonicalChartDomain M a V) :=
    d.continuousOn_symm.isOpen_inter_preimage d.open_target
      (isOpen_canonicalChartDomain M a hV)
  have hcomp := hC.comp hg (fun _ hy => hy.2.2)
  have hderiv : ContDiffOn ℝ ∞ (fderiv ℝ g)
      (d.target ∩ d.symm ⁻¹' canonicalChartDomain M a V) :=
    hg.fderiv_of_isOpen hD (by simp)
  apply (hcomp.clm_comp hderiv).congr
  intro y hy
  exact localCanonicalCoframe_inChart M a b C y hy.1 hy.2.1

set_option backward.isDefEq.respectTransparency false in
/-- The determinant square of the local coframe is smooth as an actual
section in every overlapping chart of the manifold. -/
theorem isSmoothSquaredTensorSectionOn_localCanonicalSquaredSection {n : ℕ}
    (M : SmoothManifold (2 * n)) (a : M.Point)
    {V : Set (Model (2 * n))} (hV : IsOpen V)
    {C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C V) :
    IsSmoothSquaredTensorSectionOn M (localCanonicalSquaredSection M a C)
      (canonicalChartDomain M a V) := by
  intro b
  apply (contDiffOn_coframeSquaredGenerator
    (contDiffOn_localCanonicalCoframe_inChart M a b hV hC)).congr
  intro y hy
  rw [localCanonicalSquaredSection_inChart M a b C y hy.1 hy.2.1,
    localCanonicalCoframe_inChart M a b C y hy.1 hy.2.1]

set_option backward.isDefEq.respectTransparency false in
/-- On a chart's source its actual differential is invertible, with inverse
given by the differential of the inverse chart. -/
theorem chartTangentMap_isInvertible {d : ℕ} (M : SmoothManifold d)
    (a x : M.Point) (hx : x ∈ (chartAt (Model d) a).source) :
    (M.chartTangentMap a x).IsInvertible := by
  let c := chartAt (Model d) a
  have hl := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx
  have hr := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).comp_symm_deriv (c.map_source hx)
  rw [c.left_inv hx] at hr
  exact ContinuousLinearMap.IsInvertible.of_inverse hr hl

set_option backward.isDefEq.respectTransparency false in
/-- Complex linearity in the defining chart transports to complex linearity
for the actual tangent almost complex structure. -/
theorem localCanonicalCoframe_intertwines {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (J : AlmostComplexField M)
    (C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (x : M.Point) (hx : x ∈ (chartAt (Model (2 * n)) a).source)
    (hCJ : ∀ v, C (chartAt (Model (2 * n)) a x)
      (almostComplexInChart M a J (chartAt (Model (2 * n)) a x) v) =
        coordinateComplexStructure n (C (chartAt (Model (2 * n)) a x) v))
    (v : Model (2 * n)) :
    localCanonicalCoframe M a C x (J x v) =
      coordinateComplexStructure n (localCanonicalCoframe M a C x v) := by
  let c := chartAt (Model (2 * n)) a
  have hi := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).symm_comp_deriv hx
  have hchart : almostComplexInChart M a J (c x) (M.chartTangentMap a x v) =
      M.chartTangentMap a x (J x v) := by
    change M.chartTangentMap a (c.symm (c x)) (J (c.symm (c x))
      (M.inverseChartTangentMap a (c x) (M.chartTangentMap a x v))) = _
    rw [c.left_inv hx]
    exact congrArg (fun w : Model (2 * n) => M.chartTangentMap a x (J x w))
      (congrArg (fun A => A v) hi)
  change C (c x) (M.chartTangentMap a x (J x v)) = _
  rw [← hchart]
  exact hCJ _

theorem localCanonicalSquaredSection_canonical {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (J : AlmostComplexField M)
    (C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (x : M.Point) (hx : x ∈ (chartAt (Model (2 * n)) a).source)
    (hCJ : ∀ v, C (chartAt (Model (2 * n)) a x)
      (almostComplexInChart M a J (chartAt (Model (2 * n)) a x) v) =
        coordinateComplexStructure n (C (chartAt (Model (2 * n)) a x) v)) :
    IsSquaredCanonicalTensor (J x) (localCanonicalSquaredSection M a C x) :=
  coframeSquaredGenerator_canonical _ _ (localCanonicalCoframe_intertwines M a J C x hx hCJ)

theorem localCanonicalSquaredSection_ne_zero {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point)
    (C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (x : M.Point) (hx : x ∈ (chartAt (Model (2 * n)) a).source)
    (hinv : (C (chartAt (Model (2 * n)) a x)).IsInvertible) :
    localCanonicalSquaredSection M a C x ≠ 0 :=
  coframeSquaredGenerator_ne_zero _ (hinv.comp (chartTangentMap_isInvertible M a x hx))

set_option backward.isDefEq.respectTransparency false in
theorem inverseChartTangentMap_isInvertible {d : ℕ} (M : SmoothManifold d)
    (b : M.Point) (y : Model d) (hy : y ∈ (chartAt (Model d) b).target) :
    (M.inverseChartTangentMap b y).IsInvertible := by
  let c := chartAt (Model d) b
  have hl := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) b).symm_comp_deriv (c.map_target hy)
  rw [c.right_inv hy] at hl
  have hr := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) b).comp_symm_deriv hy
  exact ContinuousLinearMap.IsInvertible.of_inverse hl hr

/-- The scalar coordinate of an actual tensor is unchanged when its tensor
and its coframe are both transported by an invertible tangent map. -/
theorem squaredCoframeCoefficient_comp {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n)
    (A : Model (2 * n) →L[ℝ] Model (2 * n)) (hA : A.IsInvertible)
    (s : SquaredCanonicalTensor n) :
    squaredCoframeCoefficient (C.comp A) (s.compContinuousLinearMap (fun _ => A)) =
      squaredCoframeCoefficient C s := by
  simp only [squaredCoframeCoefficient, hA.inverse_comp_of_right,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    hA.self_apply_inverse]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse scalar coordinate is smooth in every overlapping chart of
the actual local section, using coframe inversion and tangent-coordinate
invariance rather than an assumed scalar-coordinate regularity. -/
theorem contDiffOn_localSquaredCoframeCoefficient_inChart {n : ℕ}
    (M : SmoothManifold (2 * n)) (a b : M.Point)
    {V : Set (Model (2 * n))} (hV : IsOpen V)
    {C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C V) (hinv : ∀ y ∈ V, (C y).IsInvertible)
    (s : M.Point → SquaredCanonicalTensor n)
    (hs : IsSmoothSquaredTensorSectionOn M s (canonicalChartDomain M a V)) :
    ContDiffOn ℝ ∞ (fun y => squaredCoframeCoefficient
      (localCanonicalCoframe M a C ((chartAt (Model (2 * n)) b).symm y))
      (s ((chartAt (Model (2 * n)) b).symm y)))
      ((chartAt (Model (2 * n)) b).target ∩
        (chartAt (Model (2 * n)) b).symm ⁻¹' canonicalChartDomain M a V) := by
  have hDinv : ∀ y ∈ (chartAt (Model (2 * n)) b).target ∩
      (chartAt (Model (2 * n)) b).symm ⁻¹' canonicalChartDomain M a V,
      ((localCanonicalCoframe M a C ((chartAt (Model (2 * n)) b).symm y)).comp
        (M.inverseChartTangentMap b y)).IsInvertible := by
    intro y hy
    exact ((hinv _ hy.2.2).comp
      (chartTangentMap_isInvertible M a _ hy.2.1)).comp
        (inverseChartTangentMap_isInvertible M b y hy.1)
  apply (contDiffOn_squaredCoframeCoefficient
    (contDiffOn_localCanonicalCoframe_inChart M a b hV hC) hDinv (hs b)).congr
  intro y hy
  exact (squaredCoframeCoefficient_comp _ _
    (inverseChartTangentMap_isInvertible M b y hy.1) _).symm

private theorem contMDiffOn_of_chartCoordinates {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : SmoothManifold d) {U : Set M.Point} (hU : IsOpen U) (q : M.Point → E)
    (hq : ∀ b, ContDiffOn ℝ ∞ (q ∘ (chartAt (Model d) b).symm)
      ((chartAt (Model d) b).target ∩ (chartAt (Model d) b).symm ⁻¹' U)) :
    ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, E) ∞ q U := by
  intro x hx
  let c := chartAt (Model d) x
  have hc : x ∈ c.source := mem_chart_source _ x
  have hD : IsOpen (c.target ∩ c.symm ⁻¹' U) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target hU
  have hcx : c x ∈ c.target ∩ c.symm ⁻¹' U :=
    ⟨c.map_source hc, by simpa only [mem_preimage, c.left_inv hc] using hx⟩
  have hq' := (hq x).contDiffAt (hD.mem_nhds hcx)
  have hqM : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, E) ∞ (q ∘ c.symm) (c x) :=
    contMDiffAt_iff_contDiffAt.mpr hq'
  have hchart : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c x :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := x)).contMDiffAt
      (c.open_source.mem_nhds hc)
  have heq : q =ᶠ[𝓝 x] (q ∘ c.symm) ∘ c := by
    filter_upwards [c.open_source.mem_nhds hc] with z hz
    exact (congrArg q (c.left_inv hz)).symm
  exact ((hqM.comp x hchart).congr_of_eventuallyEq heq).contMDiffWithinAt

/-- Inversion of the actual local coframe gives a smooth scalar function
on the manifold, with native manifold smoothness. -/
theorem contMDiffOn_localSquaredCoframeCoefficient {n : ℕ}
    (M : SmoothManifold (2 * n)) (a : M.Point)
    {V : Set (Model (2 * n))} (hV : IsOpen V)
    {C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C V) (hinv : ∀ y ∈ V, (C y).IsInvertible)
    (s : M.Point → SquaredCanonicalTensor n)
    (hs : IsSmoothSquaredTensorSectionOn M s (canonicalChartDomain M a V)) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun x => squaredCoframeCoefficient (localCanonicalCoframe M a C x) (s x))
      (canonicalChartDomain M a V) :=
  contMDiffOn_of_chartCoordinates M (isOpen_canonicalChartDomain M a hV) _
    (fun b => contDiffOn_localSquaredCoframeCoefficient_inChart M a b hV hC hinv s hs)

/-- The almost complex field alone chooses a local coframe and its actual
determinant-square generator. Every smooth canonical section on this same
neighborhood then has smooth scalar coordinates in that generator. Zero
sections are allowed; nowhere-zero sections have nowhere-zero coordinates. -/
theorem exists_local_canonicalSquaredTrivialization {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : M.Point) :
    ∃ V ⊆ (chartAt (Model (2 * n)) a).target, IsOpen V ∧
      chartAt (Model (2 * n)) a a ∈ V ∧
      ∃ C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n,
        ContDiffOn ℝ ∞ C V ∧ (∀ y ∈ V, (C y).IsInvertible) ∧
        (∀ y ∈ V, ∀ v, C y (almostComplexInChart M a J y v) =
          coordinateComplexStructure n (C y v)) ∧
        IsSmoothSquaredTensorSectionOn M (localCanonicalSquaredSection M a C)
          (canonicalChartDomain M a V) ∧
        (∀ x ∈ canonicalChartDomain M a V,
          IsSquaredCanonicalTensor (J x) (localCanonicalSquaredSection M a C x)) ∧
        (∀ x ∈ canonicalChartDomain M a V, localCanonicalSquaredSection M a C x ≠ 0) ∧
        ∀ t : M.Point → SquaredCanonicalTensor n,
          IsSmoothSquaredTensorSectionOn M t (canonicalChartDomain M a V) →
          (∀ x ∈ canonicalChartDomain M a V, IsSquaredCanonicalTensor (J x) (t x)) →
          ∃ q : M.Point → ℂ,
            ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ q (canonicalChartDomain M a V) ∧
            (∀ x ∈ canonicalChartDomain M a V,
              t x = q x • localCanonicalSquaredSection M a C x) ∧
            ((∀ x ∈ canonicalChartDomain M a V, t x ≠ 0) →
              ∀ x ∈ canonicalChartDomain M a V, q x ≠ 0) := by
  let c := chartAt (Model (2 * n)) a
  have ha : c a ∈ c.target := c.map_source (mem_chart_source _ a)
  obtain ⟨C₀, V, hVc, hV, haV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_complexCoframe c.open_target ha (hJ a)
      (fun y hy => almostComplexInChart_sq M a J hJsq y hy)
  let C := fun y => projectedComplexCoframe C₀ (almostComplexInChart M a J y)
  refine ⟨V, hVc, hV, haV, C, hC, hinv, hCJ,
    isSmoothSquaredTensorSectionOn_localCanonicalSquaredSection M a hV hC, ?_, ?_⟩
  · intro x hx
    exact localCanonicalSquaredSection_canonical M a J C x hx.1 (hCJ _ hx.2)
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact localCanonicalSquaredSection_ne_zero M a C x hx.1 (hinv _ hx.2)
    · intro t ht hcanonical
      let q := fun x => squaredCoframeCoefficient (localCanonicalCoframe M a C x) (t x)
      have hrec : ∀ x ∈ canonicalChartDomain M a V,
          t x = q x • localCanonicalSquaredSection M a C x := by
        intro x hx
        exact squaredCoframe_reconstruction _
          ((hinv _ hx.2).comp (chartTangentMap_isInvertible M a x hx.1)) _
          (localCanonicalCoframe_intertwines M a J C x hx.1 (hCJ _ hx.2)) _
          (hcanonical x hx)
      refine ⟨q, contMDiffOn_localSquaredCoframeCoefficient M a hV hC hinv t ht,
        hrec, ?_⟩
      intro hnonzero x hx hq
      apply hnonzero x hx
      exact (hrec x hx).trans (by ext v; simp [hq, smul_eq_mul])

/-- Every smooth almost complex field has an actual smooth nonvanishing
local canonical-square section around every manifold point. -/
theorem exists_local_canonicalSquaredSection {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : M.Point) :
    ∃ U : Set M.Point, IsOpen U ∧ a ∈ U ∧
      ∃ s : M.Point → SquaredCanonicalTensor n,
        IsSmoothSquaredTensorSectionOn M s U ∧
        (∀ x ∈ U, IsSquaredCanonicalTensor (J x) (s x)) ∧
        (∀ x ∈ U, s x ≠ 0) := by
  obtain ⟨V, _, hV, haV, C, _, _, _, hS, hcanonical, hnonzero, _⟩ :=
    exists_local_canonicalSquaredTrivialization M J hJ hJsq a
  exact ⟨canonicalChartDomain M a V, isOpen_canonicalChartDomain M a hV,
    ⟨mem_chart_source _ a, haV⟩, localCanonicalSquaredSection M a C,
    hS, hcanonical, hnonzero⟩

namespace MaslovRepresentative

set_option backward.isDefEq.respectTransparency false in
/-- Actual Maslov sections have smooth nowhere-zero scalar coordinates in
the determinant-square generator selected by their almost complex field.
The output exposes the smooth invertible intertwining coframe and uses its
specific generator, rather than permitting the given section as generator. -/
theorem exists_local_canonicalSquaredCoordinates {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (a : M.Point) :
    ∃ V ⊆ (chartAt (Model (2 * n)) a).target, IsOpen V ∧
      chartAt (Model (2 * n)) a a ∈ V ∧
      ∃ C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n,
        ContDiffOn ℝ ∞ C V ∧ (∀ y ∈ V, (C y).IsInvertible) ∧
        (∀ y ∈ V, ∀ v, C y (almostComplexInChart M a s.J y v) =
          coordinateComplexStructure n (C y v)) ∧
        IsSmoothSquaredTensorSectionOn M (localCanonicalSquaredSection M a C)
          (canonicalChartDomain M a V) ∧
        (∀ x ∈ canonicalChartDomain M a V,
          IsSquaredCanonicalTensor (s.J x) (localCanonicalSquaredSection M a C x)) ∧
        (∀ x ∈ canonicalChartDomain M a V, localCanonicalSquaredSection M a C x ≠ 0) ∧
        ∃ q : M.Point → ℂ,
          ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ q (canonicalChartDomain M a V) ∧
          (∀ x ∈ canonicalChartDomain M a V, q x ≠ 0) ∧
          (∀ x ∈ canonicalChartDomain M a V,
            s.tensor x = q x • localCanonicalSquaredSection M a C x) := by
  obtain ⟨V, hVc, hV, haV, C, hC, hinv, hCJ, hS, hcanonical, hnonzero, hcoordinates⟩ :=
    exists_local_canonicalSquaredTrivialization M s.J s.compatible.1 s.compatible.2.1 a
  obtain ⟨q, hq, hrec, hqnonzero⟩ := hcoordinates s.tensor (s.smooth.isSmoothOn _)
    (fun x _ => s.canonical x)
  exact ⟨V, hVc, hV, haV, C, hC, hinv, hCJ, hS, hcanonical, hnonzero, q, hq,
    hqnonzero (fun x _ => s.nowhereZero x), hrec⟩

end MaslovRepresentative

end FsFltz.Geometry
