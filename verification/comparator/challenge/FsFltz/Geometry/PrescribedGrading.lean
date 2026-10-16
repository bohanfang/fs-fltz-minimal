import FsFltz.Geometry.Maslov
import FsFltz.Geometry.ToricForms

/-!
# The prescribed logarithmic and vertical-phase-zero tensor values

Source: `def:maslov`, lines 236–243. These formulas use the actual derivatives
of the marked coordinate functions and the global circle-valued angle maps.
They therefore prescribe a section on the entire completed ambient, without
choosing real-valued torus angles. Constructing the smooth canonical section
with these values remains a foundation bridge, not an input assumption.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

/-- Values of `du_j` and `dtheta_j` after the specified logarithmic marking. -/
def logarithmicTangentCoordinates {n : ℕ} (M : SmoothManifold (2 * n))
    (f : M.Point → LGSpace n) (x : M.Point) (v : M.Tangent x) :
    RealSpace n × RealSpace n :=
  (fun j => differentialCovector M (fun y => (f y).1 j) x v,
   fun j => phaseCovector M (fun y => (AddCircle.toCircle ((f y).2 j) : ℂ)) x v)

/-- Values of `dp_j` and `dtheta_j` after the specified cotangent marking. -/
def cotangentTangentCoordinates {n : ℕ} (M : SmoothManifold (2 * n))
    (f : M.Point → Cotangent n) (x : M.Point) (v : M.Tangent x) :
    RealSpace n × RealSpace n :=
  (fun j => differentialCovector M (fun y => (f y).2 j) x v,
   fun j => phaseCovector M (fun y => (AddCircle.toCircle ((f y).1 j) : ℂ)) x v)

/-- The representative is literally the pullback of the source squared
logarithmic volume form, evaluated on every pair of tangent frames. -/
def IsLogarithmicGrading {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (f : M.Point → LGSpace n) (s : MaslovRepresentative M eta) : Prop :=
  ∀ x v, s.tensor x v = coordinateSquaredVolumeValue
    (fun i => logarithmicTangentCoordinates M f x (v i))

/-- The explicit cotangent square whose value on the standard vertical
frame is one, as checked by the coordinate lemma in `Maslov.lean`. -/
def IsVerticalGrading {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (f : M.Point → Cotangent n) (s : MaslovRepresentative M eta) : Prop :=
  ∀ x v, s.tensor x v = coordinateSquaredVolumeValue
    (fun i => cotangentTangentCoordinates M f x (v i))

end FsFltz.Geometry
