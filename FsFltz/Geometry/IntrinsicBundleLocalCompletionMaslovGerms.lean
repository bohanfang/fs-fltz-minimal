import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovData
import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovRegularity
import FsFltz.Geometry.CoordinateCanonicalTensor

/-!
# Source coframe germs on the retained original completed atlas

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The smooth-extension data below concern only
the original completed local charts. They do not mention a represented
deformation or its descended fields. All matching laws are restricted to
the retained bases; end germs cover the full original signed cylinder.

This is an explicit coordinate representation of supplied source smooth
data. It does not assert existence of the toric grading or a converse from
bare boundary-manifold smoothness to real-open extensions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

namespace CompletedMaslovDimension

/-- Undo only the dimension reindexing of an original complex field. -/
def nativeField {d e : ℕ} (h : d = e) (X : CompleteLiouvilleManifold d)
    (J : AlmostComplexField (ambient h X).manifold) : AlmostComplexField X.manifold := by
  subst e
  exact J

/-- Undo only the dimension reindexing of the full original tensor. -/
def nativeTensor {d e : ℕ} {ι : Type*} [Fintype ι] (h : d = e)
    (X : CompleteLiouvilleManifold d)
    (T : (ambient h X).manifold.Point →
      ContinuousMultilinearMap ℝ (fun _ : ι => Model e) ℂ) :
    X.manifold.Point → ContinuousMultilinearMap ℝ (fun _ : ι => Model d) ℂ := by
  subst e
  exact T

/-- Inverse conjugation commutes with the dimension reindexing. -/
theorem comparison_inverse_conjugation {d e : ℕ} (h : d = e)
    (X : CompleteLiouvilleManifold d) (Y : SmoothManifold e)
    (f : X.manifold.SmoothEquiv Y) (J : AlmostComplexField (ambient h X).manifold)
    (y : Y.Point) :
    let a := (comparison h X Y f).symm
    let A := mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) a y
    A.inverse.comp ((J (a y)).comp A) =
      let D := mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) f.symm y
      D.inverse.comp ((nativeField h X J (f.symm y)).comp D) := by
  subst e
  rfl

/-- Every slot of the inverse tensor pullback commutes with reindexing. -/
theorem comparison_inverse_tensor {d e : ℕ} {ι : Type*} [Fintype ι]
    (h : d = e) (X : CompleteLiouvilleManifold d) (Y : SmoothManifold e)
    (f : X.manifold.SmoothEquiv Y)
    (T : (ambient h X).manifold.Point →
      ContinuousMultilinearMap ℝ (fun _ : ι => Model e) ℂ) (y : Y.Point) :
    let a := (comparison h X Y f).symm
    (T (a y)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) a y) =
      (nativeTensor h X T (f.symm y)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) f.symm y) := by
  subst e
  rfl

end CompletedMaslovDimension

local instance {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)

/-- The preselected source field in its original tangent model. -/
abbrev nativeJ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :=
  CompletedMaslovDimension.nativeField hdim
    ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient (S.J c t ht s hs)

/-- The preselected full source tensor in its original tangent model. -/
abbrev nativeTensor (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :=
  CompletedMaslovDimension.nativeTensor hdim
    ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient (S.tensor c t ht s hs)

end OriginalLocalCompletionMaslovData

namespace LocalCompletionFamily

/-- Differential from the original completed tangent model to one actual
interior chart, using the inverse differential of the original inclusion. -/
def interiorMaslovCoordinateDifferential
    {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}
    (F : LocalCompletionFamily P c t) (s : Parameter)
    (u w : IntrinsicInterior.Point k M) : Model (k + 1) →L[ℝ] Model (k + 1) :=
  letI := completionChartedSpace F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
  (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    (chartAt (Model (k + 1)) u) w).comp
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (interiorIn (F.native.patches s)) w).inverse

local instance {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}
    (F : LocalCompletionFamily P c t) :
    ChartedSpace (Model (k + 1)) (Band F.native.width (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace F.native.width

/-- The actual boundary–radius chart differential, including the
time-to-radius sign and inverse original full-cylinder differential. -/
def endMaslovCoordinateDifferential
    {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}
    (F : LocalCompletionFamily P c t) (s : Parameter)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (p : Band F.native.width (IntrinsicBoundary.Point k M)) :
    Model (k + 1) →L[ℝ] (Model k × ℝ) :=
  letI := completionChartedSpace F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
  (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
    (chartAt (Model k × ℝ) u) (endBandCoordinates p)).comp
    ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
        (cylinder (F.native.patches s)) p).inverse)

end LocalCompletionFamily

/-- Genuine source-local coframe and scalar extensions. These express the
source smooth-extension convention in the original spatial charts. The
original fields and all tensor slots are recovered through their actual
chart differentials, solely at retained parameters. No represented family,
comparison, descended field, or output smoothness occurs in this interface. -/
structure OriginalLocalCompletionMaslovCoframeGerms
    (S : OriginalLocalCompletionMaslovData P L hdim) : Prop where
  interior : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u w : IntrinsicInterior.Point k M),
    w ∈ (chartAt (Model (k + 1)) u).source →
    ∃ V : Set (ℝ × Model (k + 1)), IsOpen V ∧
      (s.val, chartAt (Model (k + 1)) u w) ∈ V ∧
      ∃ C : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] TangentCoordinates n,
        ContDiffOn ℝ ∞ C V ∧ (∀ z ∈ V, (C z).IsInvertible) ∧
        ∃ a : (ℝ × Model (k + 1)) → ℂ, ContDiffOn ℝ ∞ a V ∧
          ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
            (z : IntrinsicInterior.Point k M),
            z ∈ (chartAt (Model (k + 1)) u).source →
            (v.val, chartAt (Model (k + 1)) u z) ∈ V →
            let F := L.localCompletionFamily c t ht
            let x := interiorIn (F.native.patches v) z
            let B := (C (v.val, chartAt (Model (k + 1)) u z)).comp
              (F.interiorMaslovCoordinateDifferential v u z)
            (∀ ξ, B (S.nativeJ c t ht v hv x ξ) = coordinateComplexStructure n (B ξ)) ∧
            S.nativeTensor c t ht v hv x =
              a (v.val, chartAt (Model (k + 1)) u z) •
                (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => B)
  cylinder : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (p : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
    endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
    ∃ V : Set (ℝ × (Model k × ℝ)), IsOpen V ∧
      (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ V ∧
      ∃ C : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] TangentCoordinates n,
        ContDiffOn ℝ ∞ C V ∧ (∀ z ∈ V, (C z).IsInvertible) ∧
        ∃ a : (ℝ × (Model k × ℝ)) → ℂ, ContDiffOn ℝ ∞ a V ∧
          ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
            (q : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
            endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
            (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ V →
            let F := L.localCompletionFamily c t ht
            let x := cylinder (F.native.patches v) q
            let B := (C (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q))).comp
              (F.endMaslovCoordinateDifferential v u q)
            (∀ ξ, B (S.nativeJ c t ht v hv x ξ) = coordinateComplexStructure n (B ξ)) ∧
            S.nativeTensor c t ht v hv x =
              a (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) •
                (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => B)

end FsFltz.Geometry.IntrinsicSmoothBundle
