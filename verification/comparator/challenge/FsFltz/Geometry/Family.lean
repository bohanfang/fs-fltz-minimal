import FsFltz.Geometry.Smooth

/-!
# Smooth parameter families with endpoint extensions

The families of `def:chain` (source lines 163–169) and `def:maslov`
(212–232) are jointly smooth, including extensions across parameter endpoints.
The predicates below require smoothness on an actual open neighborhood of
`[0,1]` times the space. The neighborhood need not contain a uniform larger
time interval when the space is noncompact. They can therefore apply to the
completed ambient families required by `sec:lean`, lines 788–797.

These are definitions of regularity, not existence results for deformations.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry

def parameterInterval : Set ℝ := Icc 0 1

abbrev Parameter := Set.Icc (0 : ℝ) 1

def parameterZero : Parameter := ⟨0, by constructor <;> norm_num⟩

def parameterOne : Parameter := ⟨1, by constructor <;> norm_num⟩

/-- Joint smoothness with a genuine open extension around all required times
and spatial points, expressed for coefficient functions in coordinates. -/
def SmoothNearInterval {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Set E) (f : ℝ × E → F) : Prop :=
  ∃ U : Set (ℝ × E), IsOpen U ∧ parameterInterval ×ˢ s ⊆ U ∧
    ContDiffOn ℝ ∞ f U

namespace SmoothManifold

/-- A family of actual maps, smooth jointly on an open neighborhood of the
whole closed parameter interval times the source manifold. -/
def IsSmoothMapFamily {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point) : Prop :=
  ∃ U : Set (ℝ × M.Point), IsOpen U ∧ parameterInterval ×ˢ univ ⊆ U ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) (𝓘(ℝ, Model e)) ∞
      (fun tx => f tx.1 tx.2) U

/-- Forms vary smoothly in both time and space in each fixed source chart. -/
def IsSmoothFormFamily {d k : ℕ} (M : SmoothManifold d)
    (eta : ℝ → M.Form k) : Prop :=
  ∀ a, SmoothNearInterval (chartAt (Model d) a).target
    (fun ty => M.formInChart a (eta ty.1) ty.2)

/-- Vector fields vary smoothly in both time and space in each fixed chart. -/
def IsSmoothVectorFieldFamily {d : ℕ} (M : SmoothManifold d)
    (Z : (t : ℝ) → (x : M.Point) → M.Tangent x) : Prop :=
  ∀ a, SmoothNearInterval (chartAt (Model d) a).target
    (fun ty => M.vectorInChart a (Z ty.1) ty.2)

/-- Scalar families, for example the positive witnessing function on a
boundary. The chart formula also requires an open extension in time. -/
def IsSmoothScalarFamily {d : ℕ} (M : SmoothManifold d)
    (f : ℝ → M.Point → ℝ) : Prop :=
  ∀ a, SmoothNearInterval (chartAt (Model d) a).target
    (fun ty => f ty.1 ((chartAt (Model d) a).symm ty.2))

/-- Interval-indexed geometry need not satisfy its geometric inequalities
outside the interval. Its map coefficients still admit a smooth extension. -/
def IsSmoothIntervalMapFamily {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : Parameter → M.Point → N.Point) : Prop :=
  ∃ extension : ℝ → M.Point → N.Point,
    M.IsSmoothMapFamily N extension ∧ ∀ t : Parameter, extension t.val = f t

def IsSmoothIntervalFormFamily {d k : ℕ} (M : SmoothManifold d)
    (eta : Parameter → M.Form k) : Prop :=
  ∃ extension : ℝ → M.Form k,
    M.IsSmoothFormFamily extension ∧ ∀ t : Parameter, extension t.val = eta t

def IsSmoothIntervalScalarFamily {d : ℕ} (M : SmoothManifold d)
    (f : Parameter → M.Point → ℝ) : Prop :=
  ∃ extension : ℝ → M.Point → ℝ,
    M.IsSmoothScalarFamily extension ∧ ∀ t : Parameter, extension t.val = f t

def IsSmoothIntervalVectorFieldFamily {d : ℕ} (M : SmoothManifold d)
    (Z : (t : Parameter) → (x : M.Point) → M.Tangent x) : Prop :=
  ∃ extension : (t : ℝ) → (x : M.Point) → M.Tangent x,
    M.IsSmoothVectorFieldFamily extension ∧ ∀ t : Parameter, extension t.val = Z t

/-- Pull a vector field back through an actual smooth diffeomorphism. -/
def pullbackVectorField {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : M.SmoothEquiv N) (Z : (x : N.Point) → N.Tangent x) :
    (x : M.Point) → M.Tangent x :=
  fun x => mfderiv (𝓘(ℝ, Model e)) (𝓘(ℝ, Model d)) f.invFun (f x) (Z (f x))

end SmoothManifold
end FsFltz.Geometry
