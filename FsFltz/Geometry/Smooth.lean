import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Perm.Sign

/-!
# Concrete smooth extension manifolds and forms

The conventions in `geoemtric-part-fsf.tex`, lines 119–130, and the handoff
`sec:lean`, lines 783–814, are encoded using native Mathlib manifolds and
actual chart derivatives. Smooth regularity is scoped `∞`, not analytic `⊤`.
Chart independence, smooth closure, naturality and square-zero are proved in
`ExteriorDerivative.lean`; no exterior-derivative operator is supplied as input.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators
open Set

namespace FsFltz.Geometry

abbrev Model (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A boundaryless smooth extension space; compact domains below specify their
boundary by regular local defining functions in this space. -/
structure SmoothManifold (d : ℕ) where
  Point : Type
  topology : TopologicalSpace Point
  charts : @ChartedSpace (Model d) _ Point topology
  hausdorff : @T2Space Point topology
  secondCountable : @SecondCountableTopology Point topology
  smooth : @IsManifold ℝ _ (Model d) _ _ (Model d) _ (𝓘(ℝ, Model d))
    ∞ Point topology charts

attribute [instance] SmoothManifold.topology SmoothManifold.charts
  SmoothManifold.hausdorff SmoothManifold.secondCountable SmoothManifold.smooth

namespace SmoothManifold

abbrev Tangent {d : ℕ} (M : SmoothManifold d) (x : M.Point) :=
  TangentSpace (𝓘(ℝ, Model d)) x

abbrev Form {d : ℕ} (M : SmoothManifold d) (k : ℕ) :=
  (x : M.Point) → M.Tangent x [⋀^Fin k]→L[ℝ] ℝ

def chartTangentMap {d : ℕ} (M : SmoothManifold d) (a x : M.Point) :=
  mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a) x

def inverseChartTangentMap {d : ℕ} (M : SmoothManifold d) (a : M.Point) (y : Model d) :=
  mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a).symm y

/-- A form in a fixed chart, with the tangent argument transported by the
actual differential of that chart's inverse. -/
def formInChart {d k : ℕ} (M : SmoothManifold d) (a : M.Point)
    (eta : M.Form k) (y : Model d) : Model d [⋀^Fin k]→L[ℝ] ℝ :=
  (eta ((chartAt (Model d) a).symm y)).compContinuousLinearMap
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a).symm y)

def IsSmoothForm {d k : ℕ} (M : SmoothManifold d) (eta : M.Form k) : Prop :=
  ∀ a, ContDiffOn ℝ ∞ (M.formInChart a eta) (chartAt (Model d) a).target

/-- The exterior derivative is the library's alternating actual Fréchet
derivative of the chart coefficients, transported back to the tangent fiber. -/
def exteriorDerivative {d k : ℕ} (M : SmoothManifold d) (eta : M.Form k) : M.Form (k + 1) :=
  fun x => (extDeriv (M.formInChart x eta) (chartAt (Model d) x x)).compContinuousLinearMap
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) x) x)

def vectorInChart {d : ℕ} (M : SmoothManifold d) (a : M.Point)
    (Z : (x : M.Point) → M.Tangent x) (y : Model d) : Model d :=
  mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a)
    ((chartAt (Model d) a).symm y) (Z ((chartAt (Model d) a).symm y))

def IsSmoothVectorField {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) : Prop :=
  ∀ a, ContDiffOn ℝ ∞ (M.vectorInChart a Z) (chartAt (Model d) a).target

abbrev SmoothMap {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e) :=
  ContMDiffMap (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) M.Point N.Point ∞

abbrev SmoothEquiv {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e) :=
  Diffeomorph (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) M.Point N.Point ∞

def pullback {d e k : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : M.Point → N.Point) (eta : N.Form k) : M.Form k :=
  fun x => (eta (f x)).compContinuousLinearMap
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x)

/-- Smooth embedding includes immersion, as well as the induced topology. -/
structure SmoothEmbedding {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e) where
  map : M.SmoothMap N
  embedding : Topology.IsEmbedding map
  immersion : ∀ x, Function.Injective
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) map x)

def evalOne {d : ℕ} {M : SmoothManifold d} (α : M.Form 1)
    (x : M.Point) (v : M.Tangent x) : ℝ := α x (fun _ => v)

def evalTwo {d : ℕ} {M : SmoothManifold d} (eta : M.Form 2)
    (x : M.Point) (v w : M.Tangent x) : ℝ := eta x ![v, w]

def scalarDerivative {d : ℕ} (M : SmoothManifold d) (f : M.Point → ℝ)
    (x : M.Point) (v : M.Tangent x) : ℝ :=
  mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) f x v

def Nondegenerate {d : ℕ} (M : SmoothManifold d) (eta : M.Form 2) (x : M.Point) : Prop :=
  ∀ v : M.Tangent x, (∀ w, evalTwo eta x v w = 0) → v = 0

/-- The intrinsic contraction equation defining the Liouville vector. -/
def LiouvilleEquation {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1)
    (x : M.Point) (Z : M.Tangent x) : Prop :=
  ∀ v, evalTwo (M.exteriorDerivative alpha) x Z v = evalOne alpha x v

/-- A total, form-determined vector. It solves the contraction equation when
a solution exists; its default value asserts no symplecticity or existence. -/
def liouvilleVector {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1)
    (x : M.Point) : M.Tangent x := by
  classical
  exact if h : ∃ Z, M.LiouvilleEquation alpha x Z then h.choose else 0

theorem liouvilleVector_contraction {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1)
    (x : M.Point) (h : ∃ Z, M.LiouvilleEquation alpha x Z) :
    M.LiouvilleEquation alpha x (M.liouvilleVector alpha x) := by
  simp only [liouvilleVector, dite_eq_left h]
  exact h.choose_spec

theorem liouvilleEquation_unique {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1)
    (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x)
    {Z Z' : M.Tangent x} (hZ : M.LiouvilleEquation alpha x Z)
    (hZ' : M.LiouvilleEquation alpha x Z') : Z = Z' := by
  apply sub_eq_zero.mp
  apply hnd
  intro v
  have hsub := (M.exteriorDerivative alpha x).map_vecCons_sub Z Z' ![v]
  change evalTwo (M.exteriorDerivative alpha) x (Z - Z') v = 0
  rw [show evalTwo (M.exteriorDerivative alpha) x (Z - Z') v =
      evalTwo (M.exteriorDerivative alpha) x Z v -
        evalTwo (M.exteriorDerivative alpha) x Z' v from hsub]
  rw [hZ v, hZ' v, sub_self]

theorem liouvilleVector_eq {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1)
    (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x)
    {Z : M.Tangent x} (hZ : M.LiouvilleEquation alpha x Z) :
    M.liouvilleVector alpha x = Z :=
  M.liouvilleEquation_unique alpha x hnd
    (M.liouvilleVector_contraction alpha x ⟨Z, hZ⟩) hZ

def IsSymplecticOn {d : ℕ} (M : SmoothManifold d) (eta : M.Form 2)
    (s : Set M.Point) : Prop :=
  M.IsSmoothForm eta ∧ (∀ x ∈ s, M.exteriorDerivative eta x = 0) ∧
    ∀ x ∈ s, M.Nondegenerate eta x

/-- The unnormalized wedge expression `alpha ∧ (d alpha)^m`, evaluated on an
ordered tangent tuple. Its nonzero scalar normalization does not affect the
contact condition. It includes `m = 0`, where it is the one-form itself. -/
def contactVolume {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1) (m : ℕ)
    (x : M.Point) (v : Fin (2 * m + 1) → M.Tangent x) : ℝ :=
  ∑ sigma : Equiv.Perm (Fin (2 * m + 1)),
    (((Equiv.Perm.sign sigma : ℤˣ) : ℤ) : ℝ) * evalOne alpha x (v (sigma 0)) *
      ∏ i : Fin m, evalTwo (M.exteriorDerivative alpha) x
        (v (sigma (Fin.ofNat (2 * m + 1) (2 * i.val + 1))))
        (v (sigma (Fin.ofNat (2 * m + 1) (2 * i.val + 2))))

def IsContactForm {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1) (m : ℕ) : Prop :=
  d = 2 * m + 1 ∧ M.IsSmoothForm alpha ∧
    ∀ x, ∃ v : Fin (2 * m + 1) → M.Tangent x, M.contactVolume alpha m x v ≠ 0

/-- Nondegeneracy imposes no positive-dimensional condition. Thus the zero
form on a zero-dimensional ribbon is admitted by the defining predicate. -/
theorem nondegenerate_zeroDimension (M : SmoothManifold 0) (eta : M.Form 2) (x : M.Point) :
    M.Nondegenerate eta x := by
  intro v _
  exact PiLp.ext (fun j => Fin.elim0 j)

end SmoothManifold
end FsFltz.Geometry
