import FsFltz.Geometry.IntrinsicBoundary
import FsFltz.Geometry.SmoothLiouville

/-!
# Intrinsic forms and local extension data on native boundary manifolds

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–130, `def:pair`, lines 132–160, and `sec:lean`, lines 783–814.
Forms are actual alternating maps on native tangent fibers. Smooth extension
is local in each chart. `HasExteriorDerivative` spells out the actual
within-chart derivative equation; its existence is a separate foundation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

abbrev Form (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M] (r : ℕ) :=
  (x : M) → TangentSpace (𝓡∂ (k + 1)) x [⋀^Fin r]→L[ℝ] ℝ

def chartTangentMap (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (x : M) :=
  mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (e.extend (𝓡∂ (k + 1))) x

def inverseChartTangentMap
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))) (y : Model (k + 1)) :=
  mfderivWithin 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
    (e.extend (𝓡∂ (k + 1))).symm (range (𝓡∂ (k + 1))) y

def formInChart {r : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (α : Form k M r) (y : Model (k + 1)) :
    Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ :=
  (α ((e.extend (𝓡∂ (k + 1))).symm y)).compContinuousLinearMap
    (inverseChartTangentMap e y)

def vectorInChart
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x) (y : Model (k + 1)) : Model (k + 1) :=
  chartTangentMap e ((e.extend (𝓡∂ (k + 1))).symm y)
    (Z ((e.extend (𝓡∂ (k + 1))).symm y))

/-- Smoothness across the boundary consists of actual local open extensions;
no boundaryless extension manifold or vector-field extension is supplied. -/
def IsLocallyExtendibleForm {r : ℕ} (α : Form k M r) : Prop :=
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ x ∈ e.source,
      ∃ (β : Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ)
        (U : Set (Model (k + 1))),
        IsOpen U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
        β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
          (e.extend (𝓡∂ (k + 1)) x)] formInChart e α

/-- The full defining coordinate equation for an intrinsic exterior derivative.
Existence and chart covariance of this relation must be proved separately. -/
def HasExteriorDerivative {r : ℕ} (α : Form k M r) (omega : Form k M (r + 1)) : Prop :=
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M →
    ∀ y ∈ (e.extend (𝓡∂ (k + 1))).target,
      formInChart e omega y =
        extDerivWithin (formInChart e α) (e.extend (𝓡∂ (k + 1))).target y

def Nondegenerate (omega : Form k M 2) (x : M) : Prop :=
  ∀ v : TangentSpace (𝓡∂ (k + 1)) x, (∀ w, omega x ![v, w] = 0) → v = 0

def Contraction (α : Form k M 1) (omega : Form k M 2)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x) : Prop :=
  ∀ x v, omega x ![Z x, v] = α x ![v]

/-- The inverse-chart tangent derivative is inverse to the native chart derivative. -/
theorem inverseChartTangentMap_chartTangentMap
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (v : TangentSpace (𝓡∂ (k + 1)) x) :
    inverseChartTangentMap e (e.extend (𝓡∂ (k + 1)) x) (chartTangentMap e x v) = v := by
  exact congrArg (fun A => A v)
    (mfderivWithin_extend_symm_comp_mfderiv_extend'
      (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := (1 : WithTop ℕ∞)) he) hx)

theorem chartTangentMap_inverseChartTangentMap
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {y : Model (k + 1)}
    (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target) (v : Model (k + 1)) :
    chartTangentMap e ((e.extend (𝓡∂ (k + 1))).symm y)
      (inverseChartTangentMap e y v) = v := by
  exact congrArg (fun A => A v)
    (mfderiv_extend_comp_mfderivWithin_extend_symm
      (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := (1 : WithTop ℕ∞)) he) hy)

/-- Native forms are recovered from their coefficients by the actual chart differential. -/
theorem formInChart_comp_chartTangentMap {r : ℕ}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) (α : Form k M r)
    {x : M} (hx : x ∈ e.source) :
    (formInChart e α (e.extend (𝓡∂ (k + 1)) x)).compContinuousLinearMap
      (chartTangentMap e x) = α x := by
  unfold formInChart
  rw [(e.extend (𝓡∂ (k + 1))).left_inv (by simpa only [e.extend_source] using hx)]
  ext vs
  apply congrArg (α x)
  funext i
  exact inverseChartTangentMap_chartTangentMap he hx (vs i)

end FsFltz.Geometry.IntrinsicLiouville
