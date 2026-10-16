import FsFltz.Geometry.IntrinsicNativePairFamilyChain
import Mathlib.Data.List.OfFn

/-!
# The exact finite itinerary of independently presented pair families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199.
This assembly keeps every given deformation and the explicit identification
between adjacent presentations. Its original-family consumers construct those
inputs from native data; this utility alone asserts no source-family existence.
-/

namespace FsFltz.Geometry.PairDeformation

set_option backward.isDefEq.respectTransparency false

/-- Insert the actual identification between each consecutive independent
family presentation. For `m + 1` families there are `2 * m + 1` arrows. -/
def finiteJunctionChain {n : ℕ} : (m : ℕ) →
    (Q : Fin (m + 1) → PairDeformation n) →
    (I : ∀ i : Fin m, CompletionIdentification (Q i.castSucc).target (Q i.succ).source) →
    ComparisonChain (Q 0).source (Q (Fin.last m)).target
  | 0, Q, _ => Quiver.Path.nil.cons (.deformation (Q 0))
  | m + 1, Q, I =>
      ((finiteJunctionChain m (fun i => Q i.castSucc) (fun i => I i.castSucc)).cons
        (.identification (I (Fin.last m)))).cons (.deformation (Q (Fin.last (m + 1))))

@[simp] theorem finiteJunctionChain_length {n : ℕ} (m : ℕ)
    (Q : Fin (m + 1) → PairDeformation n)
    (I : ∀ i : Fin m, CompletionIdentification (Q i.castSucc).target (Q i.succ).source) :
    (finiteJunctionChain m Q I).length = 2 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (finiteJunctionChain m _ _).length + 1 + 1 = 2 * (m + 1) + 1
      rw [ih]
      omega

/-- Every source and target presentation appears in order. Even when native
endpoint data agree, the two independently chosen tuples are both recorded. -/
@[simp] theorem finiteJunctionChain_vertices {n : ℕ} (m : ℕ)
    (Q : Fin (m + 1) → PairDeformation n)
    (I : ∀ i : Fin m, CompletionIdentification (Q i.castSucc).target (Q i.succ).source) :
    (finiteJunctionChain m Q I).vertices =
      (List.ofFn Q).flatMap (fun D => [D.source, D.target]) := by
  induction m with
  | zero => simp [finiteJunctionChain, List.ofFn_succ]
  | succ m ih =>
      rw [finiteJunctionChain, Quiver.Path.vertices_cons, Quiver.Path.vertices_cons,
        ih, List.ofFn_succ' Q]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.concat_eq_append, List.append_assoc]
      rfl

end FsFltz.Geometry.PairDeformation
