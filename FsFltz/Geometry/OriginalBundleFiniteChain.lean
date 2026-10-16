import FsFltz.Geometry.OriginalBundleFiniteJunction

/-!
# Finite graded original-bundle itineraries with marking recovery

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–234; `g:chain`, lines 398–413; and
`sec:lean`, lines 788–814. Original endpoint vertices name bundles and
parameters; original arrows contain a deformation, independently supplied
original junction data, or a reverse of either. Mathlib quiver paths supply
arbitrary finite sequences, including consecutive identifications, mixed
reversals and the empty sequence. No represented pair or grading is input.

The original bundle is realized once by `bundle.realize`; every occurrence
uses that same realization. Original junction producers derive whole-ribbon
identifications and grading lifts on those choices. Compilation preserves
every arrow and the literal list of chosen endpoint tuples, and its grading
is indexed by that exact compiled path. The full retained realization at
each vertex includes both ambient and whole-ribbon recovery conclusions
for independently supplied original marking data. Different bundle labels
require an original junction even when their geometric endpoint tuples agree;
normalization of that equality into junction data is a separate correspondence.

These results transport supplied original geometric and Maslov data. They
do not construct the toric itinerary, markings, endpoint core equality or
prescribed endpoint homotopy. The geometric target remains unproved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Prefunctor

variable {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)

/-- Mapping a path preserves its number of arrows. -/
@[simp] theorem length_mapPath {a b : V} (p : Quiver.Path a b) :
    (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change (F.mapPath p).length + 1 = p.length + 1
      rw [ih]

/-- Mapping a path maps its explicit ordered endpoint list literally. -/
@[simp] theorem vertices_mapPath {a b : V} (p : Quiver.Path a b) :
    (F.mapPath p).vertices = p.vertices.map F.obj := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [mapPath_cons, Quiver.Path.vertices_cons, ih, Quiver.Path.vertices_cons]
      simp only [List.map_concat]

end Prefunctor

namespace FsFltz.Geometry

/-- Assemble grades of mapped arrows on the very same mapped quiver path.
The datum assigned to each source vertex is shared literally at a junction. -/
def gradedMapPath {n : ℕ} {V : Type*} [Quiver V]
    (F : V ⥤q WitnessedPair n) (data : ∀ v, (F.obj v).Maslov)
    (lifts : ∀ {v w} (e : v ⟶ w), GradedComparisonStep (F.map e) (data v) (data w))
    {v : V} : ∀ {w} (p : Quiver.Path v w),
      GradedComparisonChain (F.obj v) (F.mapPath p) (data v) (data w)
  | _, .nil => .nil (data v)
  | _, .cons p e => (gradedMapPath F data lifts p).cons (lifts e)

namespace IntrinsicSmoothBundle

/-- Permitted original-bundle arrows. Deformation names only its original
bundle; a junction names only original maps and homotopy. Reversal retains
the exact original arrow. -/
inductive OriginalPositiveStep (a k n : ℕ) [NeZero n] [NeZero (2 * n - 2)] : OriginalPositiveEndpoint a k n → OriginalPositiveEndpoint a k n → Type 1
  | deformation (D : OriginalPositiveBundle a k n) :
      OriginalPositiveStep a k n ⟨D, parameterZero⟩ ⟨D, parameterOne⟩
  | junction {L R : OriginalPositiveEndpoint a k n} (J : OriginalPositiveJunction L R) :
      OriginalPositiveStep a k n L R
  | reverse {L R : OriginalPositiveEndpoint a k n} (s : OriginalPositiveStep a k n L R) :
      OriginalPositiveStep a k n R L

instance (a k n : ℕ) [NeZero n] [NeZero (2 * n - 2)] : Quiver (OriginalPositiveEndpoint a k n) where
  Hom := OriginalPositiveStep a k n

namespace OriginalPositiveStep
variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]

/-- Construct each geometric arrow from original data on the retained
realizations, retaining the direction of every reverse constructor. -/
def comparisonStep {L R : OriginalPositiveEndpoint a k n} :
    OriginalPositiveStep a k n L R → ComparisonStep n L.pair R.pair
  | .deformation D => .deformation D.realize.Q
  | .junction J => .identification J.native.identification
  | .reverse s => .reverse s.comparisonStep

/-- Construct the grading of this very arrow from the original Maslov
family or homotopy. No represented deformation lift is supplied. -/
def graded {L R : OriginalPositiveEndpoint a k n} :
    (s : OriginalPositiveStep a k n L R) →
      GradedComparisonStep s.comparisonStep L.maslov R.maslov
  | .deformation D => .deformation D.realize.actualGrade
  | .junction J => .identification J.graded
  | .reverse s => .reverse s.graded

@[simp] theorem comparisonStep_reverse {L R : OriginalPositiveEndpoint a k n}
    (s : OriginalPositiveStep a k n L R) :
    s.reverse.comparisonStep = ComparisonStep.reverse s.comparisonStep := rfl

end OriginalPositiveStep

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]

/-- The original source graph maps to its single chosen geometric graph.
All incident arrows reuse the same realization of an original bundle. -/
def originalPositiveComparison (a k n : ℕ) [NeZero n] [NeZero (2 * n - 2)] :
    OriginalPositiveEndpoint a k n ⥤q WitnessedPair n where
  obj := OriginalPositiveEndpoint.pair
  map := OriginalPositiveStep.comparisonStep

namespace OriginalPositiveEndpoint
variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]

/-- Compile any finite original itinerary, including no arrows, consecutive
junctions, and reversals. Every intermediate tuple is chosen literally. -/
def comparisonChain {L R : OriginalPositiveEndpoint a k n} (C : Quiver.Path L R) :
    ComparisonChain L.pair R.pair := (originalPositiveComparison a k n).mapPath C

/-- Extend the original Maslov data along the same compiled finite path. -/
def gradedChain {L R : OriginalPositiveEndpoint a k n} (C : Quiver.Path L R) :
    GradedComparisonChain L.pair (comparisonChain C) L.maslov R.maslov :=
  gradedMapPath (originalPositiveComparison a k n) OriginalPositiveEndpoint.maslov OriginalPositiveStep.graded C

@[simp] theorem comparisonChain_nil (L : OriginalPositiveEndpoint a k n) :
    (comparisonChain (Quiver.Path.nil : Quiver.Path L L)) = Quiver.Path.nil := rfl

/-- Compilation keeps the exact last constructed geometric arrow. -/
@[simp] theorem comparisonChain_cons {L R S : OriginalPositiveEndpoint a k n}
    (C : Quiver.Path L R) (s : OriginalPositiveStep a k n R S) :
    (comparisonChain (C.cons s)) = (comparisonChain C).cons s.comparisonStep := rfl

/-- Every original arrow, including each reverse, remains one geometric
arrow. There is no replacement or insertion during compilation. -/
@[simp] theorem comparisonChain_length {L R : OriginalPositiveEndpoint a k n}
    (C : Quiver.Path L R) : (comparisonChain C).length = C.length :=
  Prefunctor.length_mapPath (originalPositiveComparison a k n) C

/-- Every intermediate pair is the chosen realization of that very original
endpoint, in the supplied order and with repetitions retained. -/
@[simp] theorem comparisonChain_vertices {L R : OriginalPositiveEndpoint a k n}
    (C : Quiver.Path L R) :
    (comparisonChain C).vertices = C.vertices.map OriginalPositiveEndpoint.pair :=
  Prefunctor.vertices_mapPath (originalPositiveComparison a k n) C

/-- A finite path in the original endpoint graph supplies a geometric
chain and grading on that exact chain. The returned realization at every
visited endpoint is the very one used by compilation; its full fields retain
both supplied-marking recovery conclusions, covariance and compact geometry. -/
theorem exists_gradedComparisonChain {L R : OriginalPositiveEndpoint a k n}
    (C : Quiver.Path L R) :
    ∃ path : ComparisonChain L.pair R.pair,
      path = (comparisonChain C) ∧ path.length = C.length ∧
      path.vertices = C.vertices.map OriginalPositiveEndpoint.pair ∧
      Nonempty (GradedComparisonChain L.pair path L.maslov R.maslov) ∧
      ∀ E ∈ C.vertices, ∃ retained : OriginalPositiveRealization E.bundle,
        retained = E.bundle.realize ∧ retained.Q.pair E.parameter = E.pair :=
  ⟨(comparisonChain C), rfl, (comparisonChain_length C), (comparisonChain_vertices C),
    ⟨(gradedChain C)⟩, fun E _ => ⟨E.bundle.realize, rfl, rfl⟩⟩

end OriginalPositiveEndpoint

/-- Permitted original-bundle arrows. Deformation names only its original
bundle; a junction names only original maps and homotopy. Reversal retains
the exact original arrow. -/
inductive OriginalZeroStep : OriginalZeroEndpoint → OriginalZeroEndpoint → Type 1
  | deformation (D : OriginalZeroBundle) :
      OriginalZeroStep ⟨D, parameterZero⟩ ⟨D, parameterOne⟩
  | junction {L R : OriginalZeroEndpoint} (J : OriginalZeroJunction L R) :
      OriginalZeroStep L R
  | reverse {L R : OriginalZeroEndpoint} (s : OriginalZeroStep L R) :
      OriginalZeroStep R L

instance : Quiver (OriginalZeroEndpoint) where
  Hom := OriginalZeroStep

namespace OriginalZeroStep
/-- Construct each geometric arrow from original data on the retained
realizations, retaining the direction of every reverse constructor. -/
def comparisonStep {L R : OriginalZeroEndpoint} :
    OriginalZeroStep L R → ComparisonStep 1 L.pair R.pair
  | .deformation D => .deformation D.realize.Q
  | .junction J => .identification J.native.identification
  | .reverse s => .reverse s.comparisonStep

/-- Construct the grading of this very arrow from the original Maslov
family or homotopy. No represented deformation lift is supplied. -/
def graded {L R : OriginalZeroEndpoint} :
    (s : OriginalZeroStep L R) →
      GradedComparisonStep s.comparisonStep L.maslov R.maslov
  | .deformation D => .deformation D.realize.actualGrade
  | .junction J => .identification J.graded
  | .reverse s => .reverse s.graded

@[simp] theorem comparisonStep_reverse {L R : OriginalZeroEndpoint}
    (s : OriginalZeroStep L R) :
    s.reverse.comparisonStep = ComparisonStep.reverse s.comparisonStep := rfl

end OriginalZeroStep

/-- The original source graph maps to its single chosen geometric graph.
All incident arrows reuse the same realization of an original bundle. -/
def originalZeroComparison :
    OriginalZeroEndpoint ⥤q WitnessedPair 1 where
  obj := OriginalZeroEndpoint.pair
  map := OriginalZeroStep.comparisonStep

namespace OriginalZeroEndpoint
/-- Compile any finite original itinerary, including no arrows, consecutive
junctions, and reversals. Every intermediate tuple is chosen literally. -/
def comparisonChain {L R : OriginalZeroEndpoint} (C : Quiver.Path L R) :
    ComparisonChain L.pair R.pair := (originalZeroComparison).mapPath C

/-- Extend the original Maslov data along the same compiled finite path. -/
def gradedChain {L R : OriginalZeroEndpoint} (C : Quiver.Path L R) :
    GradedComparisonChain L.pair (comparisonChain C) L.maslov R.maslov :=
  gradedMapPath (originalZeroComparison) OriginalZeroEndpoint.maslov OriginalZeroStep.graded C

@[simp] theorem comparisonChain_nil (L : OriginalZeroEndpoint) :
    (comparisonChain (Quiver.Path.nil : Quiver.Path L L)) = Quiver.Path.nil := rfl

/-- Compilation keeps the exact last constructed geometric arrow. -/
@[simp] theorem comparisonChain_cons {L R S : OriginalZeroEndpoint}
    (C : Quiver.Path L R) (s : OriginalZeroStep R S) :
    (comparisonChain (C.cons s)) = (comparisonChain C).cons s.comparisonStep := rfl

/-- Every original arrow, including each reverse, remains one geometric
arrow. There is no replacement or insertion during compilation. -/
@[simp] theorem comparisonChain_length {L R : OriginalZeroEndpoint}
    (C : Quiver.Path L R) : (comparisonChain C).length = C.length :=
  Prefunctor.length_mapPath (originalZeroComparison) C

/-- Every intermediate pair is the chosen realization of that very original
endpoint, in the supplied order and with repetitions retained. -/
@[simp] theorem comparisonChain_vertices {L R : OriginalZeroEndpoint}
    (C : Quiver.Path L R) :
    (comparisonChain C).vertices = C.vertices.map OriginalZeroEndpoint.pair :=
  Prefunctor.vertices_mapPath (originalZeroComparison) C

/-- A finite path in the original endpoint graph supplies a geometric
chain and grading on that exact chain. The returned realization at every
visited endpoint is the very one used by compilation; its full fields retain
both supplied-marking recovery conclusions, covariance and compact geometry. -/
theorem exists_gradedComparisonChain {L R : OriginalZeroEndpoint}
    (C : Quiver.Path L R) :
    ∃ path : ComparisonChain L.pair R.pair,
      path = (comparisonChain C) ∧ path.length = C.length ∧
      path.vertices = C.vertices.map OriginalZeroEndpoint.pair ∧
      Nonempty (GradedComparisonChain L.pair path L.maslov R.maslov) ∧
      ∀ E ∈ C.vertices, ∃ retained : OriginalZeroRealization E.bundle,
        retained = E.bundle.realize ∧ retained.Q.pair E.parameter = E.pair :=
  ⟨(comparisonChain C), rfl, (comparisonChain_length C), (comparisonChain_vertices C),
    ⟨(gradedChain C)⟩, fun E _ => ⟨E.bundle.realize, rfl, rfl⟩⟩

end OriginalZeroEndpoint

end IntrinsicSmoothBundle
end FsFltz.Geometry
