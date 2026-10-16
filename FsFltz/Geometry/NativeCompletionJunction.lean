import FsFltz.Geometry.IntrinsicNativeCompletionGrading

/-!
# Original native data for an independently chosen completion junction

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199,
`def:maslov`, lines 225–234, and `sec:lean`, lines 788–814.
The records below retain original maps, coordinate germs, end laws, and
primitive equations. A represented completion identification is constructed
by the independent-endpoint producer, rather than supplied as a record field.
Both the positive-dimensional and dimension-zero ribbon cases are included.
The endpoints and their existing completions are parameters, never replaced.

Supplying these geometric hypotheses and an original grading homotopy is
conditional foundational input. Their toric existence remains unproved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry
open IntrinsicLiouville SmoothManifold

/-- Original completed ambient maps, native boundary maps and eventual
shifted end law for two independently retained pairs. -/
structure NativeAmbientJunction {n : ℕ} (P Q : WitnessedPair n) where
  X : SmoothManifold (2 * n)
  Y : SmoothManifold (2 * n)
  boundaryDimension : ℕ
  targetBoundaryDimension : ℕ
  B : SmoothManifold boundaryDimension
  B' : SmoothManifold targetBoundaryDimension
  α : X.Form 1
  β : Y.Form 1
  S : X.SmoothEquiv P.ambientManifold
  S' : Y.SmoothEquiv Q.ambientManifold
  sourcePrimitive : X.pullback P.ambientManifold S
    P.ambientCompletion.ambient.primitive = α
  targetPrimitive : Y.pullback Q.ambientManifold S'
    Q.ambientCompletion.ambient.primitive = β
  Ψ : X.SmoothEquiv Y
  strictPrimitive : X.pullback Y Ψ β = α
  endX : B.Point × ℝ → X.Point
  endY : B'.Point × ℝ → Y.Point
  bS : B.SmoothEquiv P.ambientDomain.domain.boundary
  bS' : B'.SmoothEquiv Q.ambientDomain.domain.boundary
  sourceEnd : ∀ x t, 0 ≤ t →
    S (endX (x, t)) = P.ambientCompletion.endMap (bS x, t)
  targetEnd : ∀ x t, 0 ≤ t →
    S' (endY (x, t)) = Q.ambientCompletion.endMap (bS' x, t)
  ψ : B.SmoothEquiv B'
  shift : B.Point → ℝ
  smoothShift : ContMDiff 𝓘(ℝ, Model boundaryDimension) 𝓘(ℝ, ℝ) ∞ shift
  eventualEnd : ∀ x, ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
    Ψ (endX (x, t)) = endY (ψ x, t + shift x)

/-- Original positive-dimensional ribbon data on the actual two endpoints.
Coordinate extensions and the locally extendible native diffeomorphism
are the hypotheses used to construct its represented compact map. -/
structure NativePositiveRibbonJunction {n : ℕ} (P Q : WitnessedPair n)
    (A : NativeAmbientJunction P Q) where
  [positiveDimension : NeZero (2 * n - 2)]
  k : ℕ
  dimension : k + 1 = 2 * n - 2
  M : Type
  N : Type
  [topologyM : TopologicalSpace M]
  [topologyN : TopologicalSpace N]
  [chartedM : ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [chartedN : ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [manifoldM : IsManifold (𝓡∂ (k + 1)) ∞ M]
  [manifoldN : IsManifold (𝓡∂ (k + 1)) ∞ N]
  [compactM : CompactSpace M]
  μ : Form k M 1
  ν : Form k N 1
  eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    P.ribbonDomain.domain.Point ∞
  eN : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) N
    Q.ribbonDomain.domain.Point ∞
  sourcePrimitive : ∀ x,
    (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
        (fun y => (eM y).val) x) = μ x
  targetPrimitive : ∀ x,
    (Q.ribbonDomain.liouville.primitive (eN x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
        (fun y => (eN y).val) x) = ν x
  sourceCoordinates : HasNativeCoordinateExtensions (k := k)
    P.ribbonDomain.domain.extension (fun x => (eM x).val)
  targetCoordinates : HasNativeCoordinateExtensions (k := k)
    Q.ribbonDomain.domain.extension (fun x => (eN x).val)
  h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞
  mapGerm : IsLocallyExtendibleNativeMap (k := k) h
  scale : ℝ
  positiveScale : 0 < scale
  primitiveScale : ∀ x, (ν (h x)).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = scale • μ x
  j : M → A.B.Point
  j' : N → A.B'.Point
  sourceEmbedding : ∀ x, P.ribbonEmbedding.map (eM x).val = A.bS (j x)
  targetEmbedding : ∀ x, Q.ribbonEmbedding.map (eN x).val = A.bS' (j' x)
  ribbonSquare : ∀ x, A.ψ (j x) = j' (h x)

attribute [instance] NativePositiveRibbonJunction.topologyM NativePositiveRibbonJunction.topologyN
  NativePositiveRibbonJunction.chartedM NativePositiveRibbonJunction.chartedN
  NativePositiveRibbonJunction.manifoldM NativePositiveRibbonJunction.manifoldN
  NativePositiveRibbonJunction.compactM

/-- Rank-one native ribbons need no coordinate extension or primitive-scale
hypothesis: their one-forms vanish and the original diffeomorphism suffices. -/
structure NativeZeroRibbonJunction (P Q : WitnessedPair 1)
    (A : NativeAmbientJunction P Q) where
  M : Type
  N : Type
  [topologyM : TopologicalSpace M]
  [topologyN : TopologicalSpace N]
  [chartedM : ChartedSpace (Model 0) M]
  [chartedN : ChartedSpace (Model 0) N]
  eM : letI := P.ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞
  eN : letI := Q.ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) N Q.ribbonDomain.domain.Point ∞
  h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞
  scale : ℝ
  positiveScale : 0 < scale
  j : M → A.B.Point
  j' : N → A.B'.Point
  sourceEmbedding : ∀ x, P.ribbonEmbedding.map (eM x).val = A.bS (j x)
  targetEmbedding : ∀ x, Q.ribbonEmbedding.map (eN x).val = A.bS' (j' x)
  ribbonSquare : ∀ x, A.ψ (j x) = j' (h x)

attribute [instance] NativeZeroRibbonJunction.topologyM NativeZeroRibbonJunction.topologyN
  NativeZeroRibbonJunction.chartedM NativeZeroRibbonJunction.chartedN

namespace NativePositiveRibbonJunction

variable {n : ℕ} {P Q : WitnessedPair n} {A : NativeAmbientJunction P Q}
  (R : NativePositiveRibbonJunction P Q A)

/-- Construct the identification by the original independent endpoint
producer. The chosen pair domains and completions are retained verbatim. -/
def identification : CompletionIdentification P Q := by
  letI := R.positiveDimension
  exact (CompletionIdentification.exists_of_independentNativeEndpoints P Q
    A.X A.Y A.B A.B' A.α A.β A.S A.S' A.sourcePrimitive A.targetPrimitive
    A.Ψ A.strictPrimitive A.endX A.endY A.bS A.bS' A.sourceEnd A.targetEnd
    A.ψ A.shift A.smoothShift A.eventualEnd
    R.dimension R.μ R.ν R.eM R.eN R.sourcePrimitive R.targetPrimitive
    R.sourceCoordinates R.targetCoordinates R.h R.mapGerm R.scale
    R.positiveScale R.primitiveScale R.j R.j' R.sourceEmbedding
    R.targetEmbedding R.ribbonSquare).choose

/-- All original conjugated maps, the arbitrary shift, the constant scale,
and both directions of the prescribed native ribbon map are retained. -/
theorem identification_spec :
    R.identification.ambientEquiv = (A.S.symm.trans A.Ψ).trans A.S' ∧
    R.identification.scale = R.scale ∧
    R.identification.boundaryEquiv = (A.bS.symm.trans A.ψ).trans A.bS' ∧
    R.identification.shift = A.shift ∘ A.bS.symm ∧
    (∀ x, R.identification.ribbonEquiv.map (R.eM x).val = (R.eN (R.h x)).val) ∧
    (∀ y, R.identification.ribbonEquiv.inverse (R.eN y).val =
      (R.eM (R.h.symm y)).val) := by
  let := R.positiveDimension
  exact (CompletionIdentification.exists_of_independentNativeEndpoints P Q
    A.X A.Y A.B A.B' A.α A.β A.S A.S' A.sourcePrimitive A.targetPrimitive
    A.Ψ A.strictPrimitive A.endX A.endY A.bS A.bS' A.sourceEnd A.targetEnd
    A.ψ A.shift A.smoothShift A.eventualEnd
    R.dimension R.μ R.ν R.eM R.eN R.sourcePrimitive R.targetPrimitive
    R.sourceCoordinates R.targetCoordinates R.h R.mapGerm R.scale
    R.positiveScale R.primitiveScale R.j R.j' R.sourceEmbedding
    R.targetEmbedding R.ribbonSquare).choose_spec

end NativePositiveRibbonJunction

namespace NativeZeroRibbonJunction

variable {P Q : WitnessedPair 1} {A : NativeAmbientJunction P Q}
  (R : NativeZeroRibbonJunction P Q A)

/-- Construct the dimension-zero identification from its original native
map, using the existing independent zero-endpoint producer. -/
def identification : CompletionIdentification P Q :=
  (CompletionIdentification.exists_of_independentNativeZeroEndpoints P Q
    A.X A.Y A.B A.B' A.α A.β A.S A.S' A.sourcePrimitive A.targetPrimitive
    A.Ψ A.strictPrimitive A.endX A.endY A.bS A.bS' A.sourceEnd A.targetEnd
    A.ψ A.shift A.smoothShift A.eventualEnd R.eM R.eN R.h R.scale
    R.positiveScale R.j R.j' R.sourceEmbedding R.targetEmbedding R.ribbonSquare).choose

/-- The same original-map formulas are retained in dimension zero,
including arbitrary real end shifts and the inverse native ribbon map. -/
theorem identification_spec :
    R.identification.ambientEquiv = (A.S.symm.trans A.Ψ).trans A.S' ∧
    R.identification.scale = R.scale ∧
    R.identification.boundaryEquiv = (A.bS.symm.trans A.ψ).trans A.bS' ∧
    R.identification.shift = A.shift ∘ A.bS.symm ∧
    (∀ x, R.identification.ribbonEquiv.map (R.eM x).val = (R.eN (R.h x)).val) ∧
    (∀ y, R.identification.ribbonEquiv.inverse (R.eN y).val =
      (R.eM (R.h.symm y)).val) :=
  (CompletionIdentification.exists_of_independentNativeZeroEndpoints P Q
    A.X A.Y A.B A.B' A.α A.β A.S A.S' A.sourcePrimitive A.targetPrimitive
    A.Ψ A.strictPrimitive A.endX A.endY A.bS A.bS' A.sourceEnd A.targetEnd
    A.ψ A.shift A.smoothShift A.eventualEnd R.eM R.eN R.h R.scale
    R.positiveScale R.j R.j' R.sourceEmbedding R.targetEmbedding R.ribbonSquare).choose_spec

end NativeZeroRibbonJunction

/-- Either dimension case of an original native junction. The constructors
contain raw geometric data only; no represented permitted step is supplied. -/
inductive NativeCompletionJunction : {n : ℕ} → WitnessedPair n → WitnessedPair n → Type 1
  | positive {n : ℕ} {P Q : WitnessedPair n}
      (ambient : NativeAmbientJunction P Q)
      (ribbon : NativePositiveRibbonJunction P Q ambient) : NativeCompletionJunction P Q
  | zero {P Q : WitnessedPair 1} (ambient : NativeAmbientJunction P Q)
      (ribbon : NativeZeroRibbonJunction P Q ambient) : NativeCompletionJunction P Q

namespace NativeCompletionJunction

variable {n : ℕ} {P Q : WitnessedPair n}

/-- The original ambient data for this dimension-specific junction. -/
def ambient : NativeCompletionJunction P Q → NativeAmbientJunction P Q
  | .positive A _ => A
  | .zero A _ => A

/-- The permitted identification produced by the original native maps. -/
def identification : NativeCompletionJunction P Q → CompletionIdentification P Q
  | .positive _ R => R.identification
  | .zero _ R => R.identification

/-- The positive constant specified by the original ribbon map. -/
def scale : NativeCompletionJunction P Q → ℝ
  | .positive _ R => R.scale
  | .zero _ R => R.scale

/-- The retained ambient-map equation identifies the exact generated arrow
on which the native grading homotopy is transported. -/
theorem identification_ambientEquiv (J : NativeCompletionJunction P Q) :
    J.identification.ambientEquiv =
      (J.ambient.S.symm.trans J.ambient.Ψ).trans J.ambient.S' := by
  cases J with
  | positive A R => exact R.identification_spec.1
  | zero A R => exact R.identification_spec.1

/-- The boundary map at infinity is the conjugate of the specified native map. -/
theorem identification_boundaryEquiv (J : NativeCompletionJunction P Q) :
    J.identification.boundaryEquiv =
      (J.ambient.bS.symm.trans J.ambient.ψ).trans J.ambient.bS' := by
  cases J with
  | positive A R => exact R.identification_spec.2.2.1
  | zero A R => exact R.identification_spec.2.2.1

/-- The whole original real shift is retained, without imposing a sign. -/
theorem identification_shift (J : NativeCompletionJunction P Q) :
    J.identification.shift = J.ambient.shift ∘ J.ambient.bS.symm := by
  cases J with
  | positive A R => exact R.identification_spec.2.2.2.1
  | zero A R => exact R.identification_spec.2.2.2.1

/-- The generated compact primitive equation uses the specified constant. -/
theorem identification_scale (J : NativeCompletionJunction P Q) :
    J.identification.scale = J.scale := by
  cases J with
  | positive A R => exact R.identification_spec.2.1
  | zero A R => exact R.identification_spec.2.1

/-- An original homotopy between the retained native endpoint representatives.
Its full ambient family is input; it is not merely an equality of classes. -/
abbrev NativeGrading (J : NativeCompletionJunction P Q) (source : P.Maslov)
    (target : Q.Maslov) :=
  MaslovCompletionLift J.ambient.X J.ambient.Y
    (J.ambient.X.pullback P.ambientManifold J.ambient.S P.ambientSymplecticForm)
    (J.ambient.Y.pullback Q.ambientManifold J.ambient.S' Q.ambientSymplecticForm)
    J.ambient.Ψ (source.pullback J.ambient.S) (target.pullback J.ambient.S')

/-- Transport the supplied original homotopy onto this exact generated
identification using the producer's retained ambient-map equation. -/
def gradedLift (J : NativeCompletionJunction P Q) {source : P.Maslov}
    {target : Q.Maslov} (L : J.NativeGrading source target) :
    GradedCompletionIdentification J.identification source target :=
  J.identification.gradedLiftOfNativeConjugation J.ambient.X J.ambient.Y
    J.ambient.S J.ambient.S' J.ambient.Ψ J.identification_ambientEquiv source target L

@[simp] theorem gradedLift_family_J (J : NativeCompletionJunction P Q)
    {source : P.Maslov} {target : Q.Maslov}
    (L : J.NativeGrading source target) (t : ℝ) :
    (J.gradedLift L).family.J t =
      pullbackAlmostComplex P.ambientManifold J.ambient.X J.ambient.S.symm
        (L.family.J t) := rfl

@[simp] theorem gradedLift_family_tensor (J : NativeCompletionJunction P Q)
    {source : P.Maslov} {target : Q.Maslov}
    (L : J.NativeGrading source target) (t : ℝ) :
    (J.gradedLift L).family.tensor t =
      pullbackSquaredTensor P.ambientManifold J.ambient.X J.ambient.S.symm
        (L.family.tensor t) := rfl

end NativeCompletionJunction

end FsFltz.Geometry
