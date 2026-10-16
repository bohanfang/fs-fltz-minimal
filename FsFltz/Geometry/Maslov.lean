import FsFltz.Geometry.Family
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Concrete ambient Maslov representatives and transport

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244; `g:chain`,
lines 407–413; `sec:lean`, lines 794–814. All regularity below is `C^∞`.

The canonical fiber is represented by real alternating complex-valued forms
that are complex linear for the chosen almost complex structure. Its square
is represented inside real tensors with two separately alternating blocks.
No globally chosen square root is required. `CanonicalSquareBundle` proves
the fixed-J smooth tensor-square correspondence; `CompatibleComplexPath` and
`FixedComplexMaslov` prove compatible-structure class invariance. The
correspondence for prescribed varying completed families remains separate.
These are definitions, with no existence assertion for the geometric target.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry

abbrev AlmostComplexField {d : ℕ} (M : SmoothManifold d) :=
  (x : M.Point) → M.Tangent x →L[ℝ] M.Tangent x

def almostComplexInChart {d : ℕ} (M : SmoothManifold d) (a : M.Point)
    (J : AlmostComplexField M) (y : Model d) : Model d →L[ℝ] Model d :=
  let e := chartAt (Model d) a
  (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) e (e.symm y)).comp
    ((J (e.symm y)).comp
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) e.symm y))

def IsSmoothAlmostComplexField {d : ℕ} (M : SmoothManifold d)
    (J : AlmostComplexField M) : Prop :=
  ∀ a, ContDiffOn ℝ ∞ (almostComplexInChart M a J) (chartAt (Model d) a).target

/-- The equations in source lines 220–221, including `J² = -1`. -/
def IsCompatibleAlmostComplex {d : ℕ} (M : SmoothManifold d) (eta : M.Form 2)
    (J : AlmostComplexField M) : Prop :=
  IsSmoothAlmostComplexField M J ∧
    (∀ x v, J x (J x v) = -v) ∧
    (∀ x v w, SmoothManifold.evalTwo eta x (J x v) (J x w) =
      SmoothManifold.evalTwo eta x v w) ∧
    ∀ x v, v ≠ 0 → 0 < SmoothManifold.evalTwo eta x v (J x v)

abbrev CanonicalTensor (n : ℕ) := Model (2 * n) [⋀^Fin n]→L[ℝ] ℂ

/-- The `(n,0)` condition in real tangent coordinates. -/
def IsCanonicalTensor {n : ℕ} (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (s : CanonicalTensor n) : Prop :=
  ∀ v i, s (Function.update v i (J (v i))) = Complex.I * s v

abbrev CanonicalFiber {n : ℕ} (J : Model (2 * n) →L[ℝ] Model (2 * n)) :=
  {s : CanonicalTensor n // IsCanonicalTensor J s}

/-- Two labelled blocks avoid conflating the square with a top real form. -/
abbrev SquaredCanonicalTensor (n : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (2 * n)) ℂ

/-- A concrete tensor model for the fiber `K_J ⊗²`. Alternation is required
separately in each block, and complex linearity in every tangent slot. -/
def IsSquaredCanonicalTensor {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (s : SquaredCanonicalTensor n) : Prop :=
  (∀ v i j, i ≠ j → v (Sum.inl i) = v (Sum.inl j) → s v = 0) ∧
    (∀ v i j, i ≠ j → v (Sum.inr i) = v (Sum.inr j) → s v = 0) ∧
    ∀ v i, s (Function.update v i (J (v i))) = Complex.I * s v

abbrev SquaredCanonicalFiber {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :=
  {s : SquaredCanonicalTensor n // IsSquaredCanonicalTensor J s}

def squaredTensorInChart {n : ℕ} (M : SmoothManifold (2 * n)) (a : M.Point)
    (s : M.Point → SquaredCanonicalTensor n) (y : Model (2 * n)) :
    SquaredCanonicalTensor n :=
  (s ((chartAt (Model (2 * n)) a).symm y)).compContinuousLinearMap
    (fun _ => mfderiv (𝓘(ℝ, Model (2 * n))) (𝓘(ℝ, Model (2 * n)))
      (chartAt (Model (2 * n)) a).symm y)

def IsSmoothSquaredTensorSection {n : ℕ} (M : SmoothManifold (2 * n))
    (s : M.Point → SquaredCanonicalTensor n) : Prop :=
  ∀ a, ContDiffOn ℝ ∞ (squaredTensorInChart M a s) (chartAt (Model (2 * n)) a).target

/-- A representative carries the actual compatible structure and actual
smooth nowhere-zero tensor section on the entire ambient manifold. -/
structure MaslovRepresentative {n : ℕ} (M : SmoothManifold (2 * n)) (eta : M.Form 2) where
  J : AlmostComplexField M
  compatible : IsCompatibleAlmostComplex M eta J
  tensor : M.Point → SquaredCanonicalTensor n
  canonical : ∀ x, IsSquaredCanonicalTensor (J x) (tensor x)
  smooth : IsSmoothSquaredTensorSection M tensor
  nowhereZero : ∀ x, tensor x ≠ 0

/-- Ambient extension data on a fixed smooth presentation of the completed
family. The geometric family must supply that presentation. -/
structure MaslovFamily {n : ℕ} (M : SmoothManifold (2 * n))
    (eta : ℝ → M.Form 2) where
  J : ℝ → AlmostComplexField M
  tensor : ℝ → M.Point → SquaredCanonicalTensor n
  compatible : ∀ t ∈ Icc (0 : ℝ) 1, IsCompatibleAlmostComplex M (eta t) (J t)
  canonical : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    IsSquaredCanonicalTensor (J t x) (tensor t x)
  nowhereZero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, tensor t x ≠ 0
  smoothJ : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
    (fun p => almostComplexInChart M a (J p.1) p.2)
  smoothSection : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
    (fun p => squaredTensorInChart M a (tensor p.1) p.2)

/-- A section homotopy allows the compatible complex structure to vary. -/
structure MaslovHomotopy {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s₀ s₁ : MaslovRepresentative M eta) where
  family : MaslovFamily M (fun _ => eta)
  sourceJ : family.J 0 = s₀.J
  targetJ : family.J 1 = s₁.J
  sourceSection : family.tensor 0 = s₀.tensor
  targetSection : family.tensor 1 = s₁.tensor

/-- The explicit smooth homotopy relation. Its equivalence properties are
proved in `MaslovHomotopy.lean`; compatible-structure normalization and class
invariance are proved in `FixedComplexMaslov.lean`. -/
def MaslovHomotopic {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s₀ s₁ : MaslovRepresentative M eta) : Prop := Nonempty (MaslovHomotopy s₀ s₁)

/-- Classes generated by the concrete smooth homotopies above. The theorem
`MaslovClass.eq_iff_homotopic` in `MaslovHomotopy.lean` identifies equality
here with a single smooth homotopy using smooth endpoint collars. -/
def MaslovClass {n : ℕ} (M : SmoothManifold (2 * n)) (eta : M.Form 2) :=
  Quot (MaslovHomotopic (M := M) (eta := eta))

/-- A deformation lift must be attached to the same completed family as the
geometric step, with literal agreement of representatives at junctions. -/
structure MaslovDeformationLift {n : ℕ} (M : SmoothManifold (2 * n))
    (eta : ℝ → M.Form 2) (s₀ : MaslovRepresentative M (eta 0))
    (s₁ : MaslovRepresentative M (eta 1)) where
  family : MaslovFamily M eta
  sourceJ : family.J 0 = s₀.J
  targetJ : family.J 1 = s₁.J
  sourceSection : family.tensor 0 = s₀.tensor
  targetSection : family.tensor 1 = s₁.tensor

def pullbackAlmostComplex {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (J : AlmostComplexField N) : AlmostComplexField M :=
  fun x => (mfderiv (𝓘(ℝ, Model (2 * n))) (𝓘(ℝ, Model (2 * n))) f.invFun (f x)).comp
    ((J (f x)).comp
      (mfderiv (𝓘(ℝ, Model (2 * n))) (𝓘(ℝ, Model (2 * n))) f x))

def pullbackSquaredTensor {n : ℕ} (M N : SmoothManifold (2 * n))
    (f : M.SmoothEquiv N) (s : N.Point → SquaredCanonicalTensor n) :
    M.Point → SquaredCanonicalTensor n :=
  fun x => (s (f x)).compContinuousLinearMap
    (fun _ => mfderiv (𝓘(ℝ, Model (2 * n))) (𝓘(ℝ, Model (2 * n))) f x)

/-- The graded lift on the specified ambient completion diffeomorphism.
Primitive preservation is imposed by the geometric completion step. -/
structure MaslovCompletionLift {n : ℕ} (M N : SmoothManifold (2 * n))
    (eta : M.Form 2) (eta' : N.Form 2) (f : M.SmoothEquiv N)
    (source : MaslovRepresentative M eta) (target : MaslovRepresentative N eta') where
  family : MaslovFamily M (fun _ => eta)
  sourceJ : family.J 0 = source.J
  targetJ : family.J 1 = pullbackAlmostComplex M N f target.J
  sourceSection : family.tensor 0 = source.tensor
  targetSection : family.tensor 1 = pullbackSquaredTensor M N f target.tensor

/-- Value of the logarithmic volume form on an ordered tangent frame. This
specifies the source formula `∧ (du_j + i dθ_j)` without real-valued torus angles. -/
def coordinateVolumeValue {n : ℕ} (v : Fin n → (Fin n → ℝ) × (Fin n → ℝ)) : ℂ :=
  Matrix.det (fun i j => (v i).1 j + Complex.I * (v i).2 j)

/-- Source square and cotangent vertical-phase-zero square use this same
formula, with the first coordinates respectively `u` and `p`. Their smooth
descended representatives are constructed in `GradingRepresentatives.lean`;
the intrinsic smooth canonical-bundle correspondence remains separate. -/
def coordinateSquaredVolumeValue {n : ℕ}
    (v : (Fin n ⊕ Fin n) → (Fin n → ℝ) × (Fin n → ℝ)) : ℂ :=
  coordinateVolumeValue (fun i => v (Sum.inl i)) *
    coordinateVolumeValue (fun i => v (Sum.inr i))

/-- The ordered vertical frame in cotangent coordinates `(δp,δθ)`. -/
def verticalFrame (n : ℕ) (i : Fin n) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun j => if i = j then 1 else 0, 0)

theorem coordinateVolumeValue_verticalFrame (n : ℕ) :
    coordinateVolumeValue (verticalFrame n) = 1 := by
  have h : (fun i j : Fin n => ((verticalFrame n i).1 j : ℂ) +
      Complex.I * ((verticalFrame n i).2 j : ℂ)) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [verticalFrame, Matrix.one_apply, hij]
  unfold coordinateVolumeValue
  rw [h, Matrix.det_one]

/-- In particular the square has the prescribed vertical phase zero. -/
theorem coordinateSquaredVolumeValue_verticalFrame (n : ℕ) :
    coordinateSquaredVolumeValue (fun i => verticalFrame n (i.elim id id)) = 1 := by
  simp [coordinateSquaredVolumeValue, coordinateVolumeValue_verticalFrame]

end FsFltz.Geometry
