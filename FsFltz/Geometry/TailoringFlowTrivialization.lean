import FsFltz.Geometry.TailoringHorizontalFlow
import FsFltz.Geometry.MarkedFlowTrivialization

/-!
# Literal tailoring total-space homeomorphism

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–993.
The constructed flow trivializes the actual total subset and carries its
marked boundary onto the product boundary subset. A smooth compact-domain
family and completed pair deformation require further native smooth data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- The actual marked tailoring total space is homeomorphic over the whole
closed interval to the product with its zero fiber. The same homeomorphism
preserves the literal truncation boundary. -/
theorem tailoringFamily_exists_uniform_truncatedTotalSpace_homeomorph
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      ∃ e : {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ A} ≃ₜ
        Parameter × {x : LGSpace n | tailoringFamily I β 0 x = 1 ∧ φ x.1 ≤ A},
        (∀ p, (e p).1.val = p.val.1) ∧
        ∀ p, φ (e p).2.val.1 = A ↔ φ p.val.2.1 = A := by
  obtain ⟨F, hF, β₀, hβ₀, hflow⟩ := tailoringFamily_exists_uniform_compact_transport
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ A hA
  obtain ⟨Φ, _hΦ, htransport⟩ := hflow β hβ A hA
  let S : ℝ → Set (LGSpace n) := fun s =>
    {x | tailoringFamily I β s x = 1 ∧ φ x.1 ≤ A}
  have hpres : ∀ p : ℝ × LGSpace n, p.1 ∈ Icc (0 : ℝ) 1 → p.2 ∈ S p.1 →
      ∀ t : ℝ, p.1 + t ∈ Icc (0 : ℝ) 1 →
        (Φ t p).1 = p.1 + t ∧ (Φ t p).2 ∈ S (Φ t p).1 := by
    intro p hp hs t ht
    have h := htransport p hp hs.1 hs.2 t ht
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  refine ⟨flowTotalSpaceHomeomorph S Φ hpres, fun _ => rfl, ?_⟩
  intro p
  change φ (Φ (-p.val.1) p.val).2.1 = A ↔ φ p.val.2.1 = A
  exact (htransport p.val p.property.1 p.property.2.1 p.property.2.2
    (-p.val.1) (by simp)).2.2.2.1

end FsFltz
