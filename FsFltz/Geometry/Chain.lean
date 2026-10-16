import FsFltz.Geometry.Deformation
import FsFltz.Geometry.Identification
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Finite geometric comparison chains

This encodes the permitted steps and literal endpoint matching of
`def:chain`, source lines 163–200, using Mathlib's finite quiver paths.
The arrows contain actual geometric deformations or completion maps.
Equality of embedded cores is not a constructor.
-/

namespace FsFltz.Geometry

/-- Every step contains its geometric data. Reversal retains the same data
and records the opposite direction, as explicitly allowed in the source. -/
inductive ComparisonStep (n : ℕ) : WitnessedPair n → WitnessedPair n → Type 1
  | deformation (D : PairDeformation n) : ComparisonStep n D.source D.target
  | identification {P Q : WitnessedPair n} (h : CompletionIdentification P Q) :
      ComparisonStep n P Q
  | reverse {P Q : WitnessedPair n} (s : ComparisonStep n P Q) : ComparisonStep n Q P

instance (n : ℕ) : Quiver (WitnessedPair n) where
  Hom := ComparisonStep n

/-- A finite list of actual steps whose successive endpoint tuples agree
literally by their dependent types. The full list of intermediate pairs is
available as `Quiver.Path.vertices`; no arbitrary reachability relation is input. -/
abbrev ComparisonChain {n : ℕ} (P Q : WitnessedPair n) := Quiver.Path P Q

end FsFltz.Geometry
