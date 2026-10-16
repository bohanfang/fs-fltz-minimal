import FsFltz.Geometry.NativeCompletionJunction
import Mathlib.Data.List.OfFn

/-!
# Finite assembly of original native completion junctions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 191–199,
`def:maslov`, lines 225–234, `g:chain`, lines 398–413, and
`sec:lean`, lines 788–814. A finite itinerary contains already constructed
completed deformations, original native junction data, and reversals. The
independent-endpoint producer constructs each identification on its exact
given pairs. Recursive assembly retains every intermediate tuple, arrow,
orientation, and step count. Recursive grading transports supplied native
homotopies on those very identifications, sharing junction representatives
literally.

This is conditional assembly and transport. The deformation families and
their lifts are already represented inputs; this module does not construct
them from arbitrary original source families. Existence of the target's
itinerary, supplied homotopies, markings and prescribed endpoint classes
remains a separate geometric obligation.
-/

noncomputable section

namespace FsFltz.Geometry

/-- An itinerary arrow contains an already constructed completed deformation
or the original native data that produce its identification. Reversal keeps
the exact original arrow. There is no represented identification constructor. -/
inductive NativeComparisonStep (n : ℕ) : WitnessedPair n → WitnessedPair n → Type 1
  | deformation (D : PairDeformation n) : NativeComparisonStep n D.source D.target
  | junction {P Q : WitnessedPair n} (J : NativeCompletionJunction P Q) :
      NativeComparisonStep n P Q
  | reverse {P Q : WitnessedPair n} (step : NativeComparisonStep n P Q) :
      NativeComparisonStep n Q P

namespace NativeComparisonStep

/-- Native junction arrows invoke their actual independent-endpoint producer;
deformations and reversal retain the given geometric data. -/
def comparisonStep {n : ℕ} {P Q : WitnessedPair n} :
    NativeComparisonStep n P Q → ComparisonStep n P Q
  | .deformation D => .deformation D
  | .junction J => .identification J.identification
  | .reverse step => .reverse step.comparisonStep

@[simp] theorem comparisonStep_deformation {n : ℕ} (D : PairDeformation n) :
    (deformation D).comparisonStep = ComparisonStep.deformation D := rfl

@[simp] theorem comparisonStep_junction {n : ℕ} {P Q : WitnessedPair n}
    (J : NativeCompletionJunction P Q) :
    (junction J).comparisonStep = ComparisonStep.identification J.identification := rfl

@[simp] theorem comparisonStep_reverse {n : ℕ} {P Q : WitnessedPair n}
    (step : NativeComparisonStep n P Q) :
    step.reverse.comparisonStep = ComparisonStep.reverse step.comparisonStep := rfl

end NativeComparisonStep

/-- An arbitrary finite itinerary with literal endpoint matching. Its arrows
retain the independent native maps; a path of represented steps is not input. -/
inductive NativeComparisonChain {n : ℕ} (P : WitnessedPair n) : WitnessedPair n → Type 1
  | nil : NativeComparisonChain P P
  | cons {Q R : WitnessedPair n} (initial : NativeComparisonChain P Q)
      (last : NativeComparisonStep n Q R) : NativeComparisonChain P R

namespace NativeComparisonChain

variable {n : ℕ} {P Q : WitnessedPair n}

/-- Compile every original junction, preserving each exact pair and arrow. -/
def comparisonChain {Q : WitnessedPair n} : NativeComparisonChain P Q → ComparisonChain P Q
  | .nil => .nil
  | .cons initial last => initial.comparisonChain.cons last.comparisonStep

/-- The number of supplied itinerary arrows, including each reverse once. -/
def length {Q : WitnessedPair n} : NativeComparisonChain P Q → ℕ
  | .nil => 0
  | .cons initial _ => initial.length + 1

/-- The explicit source list of exact intermediate pair tuples. -/
def vertices {Q : WitnessedPair n} : NativeComparisonChain P Q → List (WitnessedPair n)
  | .nil => [P]
  | @cons _ _ _ R initial _ => initial.vertices.concat R

@[simp] theorem comparisonChain_nil :
    (nil : NativeComparisonChain P P).comparisonChain = Quiver.Path.nil := rfl

/-- Compilation retains the exact last arrow produced from its original
maps, rather than replacing the itinerary by another path with equal endpoints. -/
@[simp] theorem comparisonChain_cons {R : WitnessedPair n}
    (initial : NativeComparisonChain P Q) (last : NativeComparisonStep n Q R) :
    (initial.cons last).comparisonChain =
      initial.comparisonChain.cons last.comparisonStep := rfl

/-- No arrow is lost or inserted by compilation, at any finite length. -/
@[simp] theorem length_comparisonChain (C : NativeComparisonChain P Q) :
    C.comparisonChain.length = C.length := by
  induction C with
  | nil => rfl
  | cons initial last ih =>
      change initial.comparisonChain.length + 1 = initial.length + 1
      rw [ih]

/-- Every intermediate tuple agrees literally with the supplied finite list,
including repeated vertices and the endpoints of reversed arrows. -/
@[simp] theorem vertices_comparisonChain (C : NativeComparisonChain P Q) :
    C.comparisonChain.vertices = C.vertices := by
  induction C with
  | nil => rfl
  | cons initial last ih =>
      change (initial.comparisonChain.cons last.comparisonStep).vertices = _
      rw [Quiver.Path.vertices_cons, ih]
      rfl

/-- Build an itinerary directly from any finite indexed list of independently
chosen pairs and original arrows on its consecutive literal endpoints. -/
def ofFiniteSteps : (m : ℕ) → (pairs : Fin (m + 1) → WitnessedPair n) →
    (steps : ∀ i : Fin m, NativeComparisonStep n (pairs i.castSucc) (pairs i.succ)) →
      NativeComparisonChain (pairs 0) (pairs (Fin.last m))
  | 0, _, _ => .nil
  | m + 1, pairs, steps =>
      (ofFiniteSteps m (fun i => pairs i.castSucc) (fun i => steps i.castSucc)).cons
        (steps (Fin.last m))

@[simp] theorem length_ofFiniteSteps (m : ℕ)
    (pairs : Fin (m + 1) → WitnessedPair n)
    (steps : ∀ i : Fin m, NativeComparisonStep n (pairs i.castSucc) (pairs i.succ)) :
    (ofFiniteSteps m pairs steps).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (ofFiniteSteps m _ _).length + 1 = m + 1
      rw [ih]

/-- The finite-index adapter retains the supplied vertex list in order. -/
@[simp] theorem vertices_ofFiniteSteps (m : ℕ)
    (pairs : Fin (m + 1) → WitnessedPair n)
    (steps : ∀ i : Fin m, NativeComparisonStep n (pairs i.castSucc) (pairs i.succ)) :
    (ofFiniteSteps m pairs steps).vertices = List.ofFn pairs := by
  induction m with
  | zero => simp [ofFiniteSteps, vertices, List.ofFn_succ]
  | succ m ih =>
      change (ofFiniteSteps m _ _).vertices.concat (pairs (Fin.last (m + 1))) = _
      rw [ih]
      exact (List.ofFn_succ' pairs).symm

end NativeComparisonChain

/-- The supplied grading of the original itinerary arrow. For a native
junction, the homotopy is on the original completed ambients. Deformation
lifts are conditional, already represented completed-family inputs. -/
inductive NativeGradedComparisonStep {n : ℕ} :
    {P Q : WitnessedPair n} → NativeComparisonStep n P Q → P.Maslov → Q.Maslov → Type 1
  | deformation {D : PairDeformation n} {source : D.source.Maslov}
      {target : D.target.Maslov} (lift : GradedPairDeformation D source target) :
      NativeGradedComparisonStep (.deformation D) source target
  | junction {P Q : WitnessedPair n} {J : NativeCompletionJunction P Q}
      {source : P.Maslov} {target : Q.Maslov} (lift : J.NativeGrading source target) :
      NativeGradedComparisonStep (.junction J) source target
  | reverse {P Q : WitnessedPair n} {step : NativeComparisonStep n P Q}
      {source : P.Maslov} {target : Q.Maslov}
      (lift : NativeGradedComparisonStep step source target) :
      NativeGradedComparisonStep (.reverse step) target source

namespace NativeGradedComparisonStep

/-- Each original homotopy grades its very generated arrow. Reverse uses the
grading of the original arrow with its literal representatives exchanged. -/
def grading {n : ℕ} {P Q : WitnessedPair n} {step : NativeComparisonStep n P Q}
    {source : P.Maslov} {target : Q.Maslov} :
    NativeGradedComparisonStep step source target →
      GradedComparisonStep step.comparisonStep source target
  | .deformation lift => .deformation lift
  | .junction lift => .identification (NativeCompletionJunction.gradedLift _ lift)
  | .reverse lift => .reverse lift.grading

end NativeGradedComparisonStep

/-- Supplied grading data on this exact original finite itinerary. One
representative is shared literally at every junction; existence of the
original extensions and homotopies is not asserted by this definition. -/
inductive NativeGradedComparisonChain {n : ℕ} (P : WitnessedPair n) :
    {Q : WitnessedPair n} → NativeComparisonChain P Q → P.Maslov → Q.Maslov → Type 1
  | nil (datum : P.Maslov) : NativeGradedComparisonChain P .nil datum datum
  | cons {Q R : WitnessedPair n} {path : NativeComparisonChain P Q}
      {step : NativeComparisonStep n Q R} {source : P.Maslov}
      {junction : Q.Maslov} {target : R.Maslov}
      (initial : NativeGradedComparisonChain P path source junction)
      (last : NativeGradedComparisonStep step junction target) :
      NativeGradedComparisonChain P (path.cons step) source target

namespace NativeGradedComparisonChain

variable {n : ℕ} {P Q : WitnessedPair n} {C : NativeComparisonChain P Q}
  {source : P.Maslov} {target : Q.Maslov}

/-- Assemble transported native homotopies and the supplied deformation lifts
on the exact compiled geometric chain, for arbitrary finite length. -/
def grading {Q : WitnessedPair n} {C : NativeComparisonChain P Q}
    {source : P.Maslov} {target : Q.Maslov} :
    NativeGradedComparisonChain P C source target →
    GradedComparisonChain P C.comparisonChain source target
  | .nil datum => .nil datum
  | .cons initial last => initial.grading.cons last.grading

/-- Supply the endpoint representatives and original lifts on a finite
indexed itinerary. Recursion shares each indexed junction representative
literally, without choosing class representatives during compilation. -/
def ofFiniteSteps : (m : ℕ) → (pairs : Fin (m + 1) → WitnessedPair n) →
    (steps : ∀ i : Fin m, NativeComparisonStep n (pairs i.castSucc) (pairs i.succ)) →
    (data : ∀ i : Fin (m + 1), (pairs i).Maslov) →
    (lifts : ∀ i : Fin m,
      NativeGradedComparisonStep (steps i) (data i.castSucc) (data i.succ)) →
      NativeGradedComparisonChain (pairs 0)
        (NativeComparisonChain.ofFiniteSteps m pairs steps) (data 0) (data (Fin.last m))
  | 0, _, _, data, _ => .nil (data 0)
  | m + 1, pairs, steps, data, lifts =>
      (ofFiniteSteps m (fun i => pairs i.castSucc) (fun i => steps i.castSucc)
        (fun i => data i.castSucc) (fun i => lifts i.castSucc)).cons (lifts (Fin.last m))

/-- Conditional finite assembly retains the original tuple list and arrow
count and equips that very geometric chain with the supplied grading.
This does not assert existence of a toric itinerary or original homotopies. -/
theorem exists_gradedComparisonChain (G : NativeGradedComparisonChain P C source target) :
    ∃ D : ComparisonChain P Q,
      D = C.comparisonChain ∧ D.length = C.length ∧ D.vertices = C.vertices ∧
      Nonempty (GradedComparisonChain P D source target) :=
  ⟨C.comparisonChain, rfl, C.length_comparisonChain, C.vertices_comparisonChain,
    ⟨G.grading⟩⟩

/-- Any finite indexed original itinerary with supplied lifts gives a
geometric comparison with exactly that many arrows and the original list
of pair tuples; its grading is on that same generated path. -/
theorem exists_ofFiniteSteps (m : ℕ) (pairs : Fin (m + 1) → WitnessedPair n)
    (steps : ∀ i : Fin m, NativeComparisonStep n (pairs i.castSucc) (pairs i.succ))
    (data : ∀ i : Fin (m + 1), (pairs i).Maslov)
    (lifts : ∀ i : Fin m,
      NativeGradedComparisonStep (steps i) (data i.castSucc) (data i.succ)) :
    ∃ D : ComparisonChain (pairs 0) (pairs (Fin.last m)),
      D = (NativeComparisonChain.ofFiniteSteps m pairs steps).comparisonChain ∧
      D.length = m ∧ D.vertices = List.ofFn pairs ∧
      Nonempty (GradedComparisonChain (pairs 0) D (data 0) (data (Fin.last m))) := by
  let C := NativeComparisonChain.ofFiniteSteps m pairs steps
  let G := ofFiniteSteps m pairs steps data lifts
  exact ⟨C.comparisonChain, rfl,
    C.length_comparisonChain.trans (NativeComparisonChain.length_ofFiniteSteps m pairs steps),
    C.vertices_comparisonChain.trans (NativeComparisonChain.vertices_ofFiniteSteps m pairs steps),
    ⟨G.grading⟩⟩

end NativeGradedComparisonChain

end FsFltz.Geometry
