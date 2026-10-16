import FsFltz.Geometry.MaslovTransport
import FsFltz.Geometry.Chain

/-!
# Maslov data on the same finite geometric chain

Source: `def:maslov`, lines 225–232, and `g:chain`, lines 398–413.
Every grading lift is indexed by the actual geometric arrow. A graded
path is indexed by the actual finite `ComparisonChain`; each junction has
one representative shared literally by the preceding and following lifts.
This is the data required by the target, not a theorem constructing it.
-/

namespace FsFltz.Geometry

/-- The lift of one specified geometric step. Reversal retains the lift of
the original arrow with its endpoint representatives exchanged. -/
inductive GradedComparisonStep {n : ℕ} :
    {P Q : WitnessedPair n} → ComparisonStep n P Q → P.Maslov → Q.Maslov → Type 1
  | deformation {D : PairDeformation n} {source : D.source.Maslov} {target : D.target.Maslov}
      (lift : GradedPairDeformation D source target) :
      GradedComparisonStep (.deformation D) source target
  | identification {P Q : WitnessedPair n} {h : CompletionIdentification P Q}
      {source : P.Maslov} {target : Q.Maslov}
      (lift : GradedCompletionIdentification h source target) :
      GradedComparisonStep (.identification h) source target
  | reverse {P Q : WitnessedPair n} {step : ComparisonStep n P Q}
      {source : P.Maslov} {target : Q.Maslov}
      (lift : GradedComparisonStep step source target) :
      GradedComparisonStep (.reverse step) target source

/-- The grading data of this exact geometric path, with a single datum at
every intermediate tuple. The zero-length path preserves its representative. -/
inductive GradedComparisonChain {n : ℕ} (P : WitnessedPair n) :
    {Q : WitnessedPair n} → ComparisonChain P Q → P.Maslov → Q.Maslov → Type 1
  | nil (datum : P.Maslov) : GradedComparisonChain P Quiver.Path.nil datum datum
  | cons {Q R : WitnessedPair n} {path : ComparisonChain P Q}
      {step : ComparisonStep n Q R} {source : P.Maslov} {junction : Q.Maslov} {target : R.Maslov}
      (initial : GradedComparisonChain P path source junction)
      (last : GradedComparisonStep step junction target) :
      GradedComparisonChain P (path.cons step) source target

end FsFltz.Geometry
