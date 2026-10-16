import FsFltz.Geometry.MarkedHorizontalFlow

/-!
# Literal total-space trivialization from horizontal transport

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–993.
The inverse is constructed by running the same flow back to parameter zero.
This is a topological trivialization; native smooth compact-domain data and
joint completion markings are separate obligations.
-/

noncomputable section
open Set

namespace FsFltz.Geometry

variable {X : Type*} [TopologicalSpace X]

/-- Full-interval horizontal transport gives an actual homeomorphism from
the literal total subset to the interval times its zero fiber. -/
def flowTotalSpaceHomeomorph (S : ℝ → Set X) (Φ : Flow ℝ (ℝ × X))
    (htransport : ∀ p : ℝ × X, p.1 ∈ Icc (0 : ℝ) 1 → p.2 ∈ S p.1 →
      ∀ t : ℝ, p.1 + t ∈ Icc (0 : ℝ) 1 →
        (Φ t p).1 = p.1 + t ∧ (Φ t p).2 ∈ S (Φ t p).1) :
    {p : ℝ × X | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ S p.1} ≃ₜ
      Parameter × {x : X | x ∈ S 0} := by
  let T := {p : ℝ × X | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ S p.1}
  have hback (p : T) : (Φ (-p.val.1) p.val).1 = 0 ∧
      (Φ (-p.val.1) p.val).2 ∈ S 0 := by
    have h := htransport p.val p.property.1 p.property.2 (-p.val.1) (by simp)
    have heq : (Φ (-p.val.1) p.val).1 = 0 := by simpa only [add_neg_cancel] using h.1
    exact ⟨heq, by simpa only [heq] using h.2⟩
  have hforward (p : Parameter × {x : X | x ∈ S 0}) :
      (Φ p.1.val (0, p.2.val)).1 = p.1.val ∧
      (Φ p.1.val (0, p.2.val)).2 ∈ S (Φ p.1.val (0, p.2.val)).1 := by
    simpa only [zero_add] using
      htransport (0, p.2.val) (by simp) p.2.property p.1.val
        (by simpa only [zero_add] using p.1.property)
  let f : T → Parameter × {x : X | x ∈ S 0} := fun p =>
    (⟨p.val.1, p.property.1⟩, ⟨(Φ (-p.val.1) p.val).2, (hback p).2⟩)
  let g : Parameter × {x : X | x ∈ S 0} → T := fun p =>
    ⟨Φ p.1.val (0, p.2.val), by rw [(hforward p).1]; exact p.1.property, (hforward p).2⟩
  refine
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro p
    apply Subtype.ext
    change Φ p.val.1 (0, (Φ (-p.val.1) p.val).2) = p.val
    have heq : (0, (Φ (-p.val.1) p.val).2) = Φ (-p.val.1) p.val :=
      Prod.ext (hback p).1.symm rfl
    rw [heq, ← Φ.map_add, add_neg_cancel, Flow.map_zero_apply]
  · intro p
    apply Prod.ext
    · apply Subtype.ext
      exact (hforward p).1
    · apply Subtype.ext
      change (Φ (-(Φ p.1.val (0, p.2.val)).1)
        (Φ p.1.val (0, p.2.val))).2 = p.2.val
      rw [(hforward p).1, ← Φ.map_add, neg_add_cancel, Flow.map_zero_apply]
  · exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp
        (Φ.continuous (continuous_fst.comp continuous_subtype_val).neg
          continuous_subtype_val)).subtype_mk _)
  · exact (Φ.continuous (continuous_subtype_val.comp continuous_fst)
      (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp]
theorem flowTotalSpaceHomeomorph_parameter (S : ℝ → Set X) (Φ : Flow ℝ (ℝ × X))
    (htransport : ∀ p : ℝ × X, p.1 ∈ Icc (0 : ℝ) 1 → p.2 ∈ S p.1 →
      ∀ t : ℝ, p.1 + t ∈ Icc (0 : ℝ) 1 →
        (Φ t p).1 = p.1 + t ∧ (Φ t p).2 ∈ S (Φ t p).1)
    (p : {p : ℝ × X | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ S p.1}) :
    (flowTotalSpaceHomeomorph S Φ htransport p).1.val = p.val.1 := rfl

end FsFltz.Geometry
