import FsFltz.Geometry.TailoringHorizontalGluing
import FsFltz.Geometry.MarkedHorizontalFlow
import FsFltz.Geometry.MarkedCurveConfinement

/-!
# Constructed all-real smooth flow for the marked tailoring family

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–993.
Compact support gives a complete auxiliary flow; its native differential
equations agree with the actual tailoring equations near the compact family.
The open differential collars give transport across the whole parameter
interval, exact inverse maps, and preservation of the truncation boundary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set Filter

namespace FsFltz
open Geometry

variable {n : ℕ}

/-- The actual compact tailoring family constructs a globally smooth all-real
auxiliary flow whose field obeys the original parameter/fiber equations near
the family and the potential equation near its truncation boundary. -/
theorem tailoringFamily_exists_uniform_compact_horizontalFlow
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
      letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      letI : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
      letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
        inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
      letI : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
        rw [modelWithCornersSelf_prod]
        exact inferInstanceAs
          (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
      ∃ (O B : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p)
        (Φ : Flow ℝ (ℝ × LGSpace n)),
        IsOpen O ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ A} ⊆ O ∧
        IsOpen B ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 = A} ⊆ B ∧
        ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
          (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n))
            (ℝ × LGSpace n))) ∧
        (∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
          (fun q : ℝ × LGSpace n => (q.1, tailoringFamily I β q.1 q.2)) p (V p) = (1, 0)) ∧
        (∀ p ∈ O ∩ B, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × LGSpace n => φ q.2.1) p (V p) = 0) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n)))
          𝓘(ℝ, ℝ × Model (2 * n)) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => Φ p.1 p.2) ∧
        ∀ p, IsMIntegralCurve (fun t => Φ t p) V := by
  obtain ⟨F, hF, β₀, hβ₀, hfield⟩ := tailoringFamily_exists_uniform_compact_horizontalField
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ A hA
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  let : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
  let : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs
      (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
  obtain ⟨O, B, V, hO, hCO, hB, hCB, hV, hder, hρ⟩ := hfield β hβ A hA
  have hcompact := isCompact_tailoringFamily_truncatedTotalSpace
    hφ hEnd1 hEnd hhom hc hlower hL hend I β A
  obtain ⟨P, K, W, Φ, hP, hCP, hPO, _hK, _hW, _hzero, heq, hΦ, hode⟩ :=
    exists_supported_horizontalFlow_near_compact hcompact hO hCO V hV.contMDiffOn
  refine ⟨P, B, W, Φ, hP, hCP, hB, hCB, _hW, ?_, ?_, hΦ, hode⟩
  · intro p hp
    rw [heq p hp]
    exact hder p (hPO hp)
  · intro p hp
    rw [heq p hp.1]
    exact hρ p ⟨hPO hp.1, hp.2⟩

/-- Actual transport throughout the full parameter interval. The same smooth
flow transports every point of the literal compact ribbon family, preserves
its boundary in both directions, and has the displayed pointwise inverse.
Its time and fiber equations are consequences of the constructed field,
not hypotheses on a supplied trivialization. -/
theorem tailoringFamily_exists_uniform_compact_transport
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
      letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      letI : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
      letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
        inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
      letI : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
        rw [modelWithCornersSelf_prod]
        exact inferInstanceAs
          (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
      ∃ Φ : Flow ℝ (ℝ × LGSpace n),
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n)))
          𝓘(ℝ, ℝ × Model (2 * n)) ∞
          (fun q : ℝ × (ℝ × LGSpace n) => Φ q.1 q.2) ∧
        ∀ p : ℝ × LGSpace n, p.1 ∈ Icc (0 : ℝ) 1 →
          tailoringFamily I β p.1 p.2 = 1 → φ p.2.1 ≤ A →
          ∀ t : ℝ, p.1 + t ∈ Icc (0 : ℝ) 1 →
            (Φ t p).1 = p.1 + t ∧
            tailoringFamily I β (Φ t p).1 (Φ t p).2 = 1 ∧
            φ (Φ t p).2.1 ≤ A ∧
            (φ (Φ t p).2.1 = A ↔ φ p.2.1 = A) ∧
            Φ (-t) (Φ t p) = p := by
  obtain ⟨F, hF, β₀, hβ₀, hflow⟩ := tailoringFamily_exists_uniform_compact_horizontalFlow
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ A hA
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  let : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
  let : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs
      (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
  obtain ⟨O, B, V, Φ, hO, hCO, hB, hCB, _hV, hder, hpot, hΦ, hode⟩ :=
    hflow β hβ A hA
  have hτ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => p.1) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hf : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => tailoringFamily I β p.1 p.2) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_tailoringFamily_native_joint I β
  have hρ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => φ p.2.1) := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiff_potentialValue hφ).comp contMDiff_snd
  have hpres := horizontalFlow_preserves_parameter_truncation
    (fun p : ℝ × LGSpace n => p.1) (fun p : ℝ × LGSpace n => φ p.2.1)
    (fun p : ℝ × LGSpace n => tailoringFamily I β p.1 p.2)
    hτ hρ hf 1 A O B hO hB hCO hCB V Φ hode hder hpot
  refine ⟨Φ, hΦ, ?_⟩
  intro p hp hpf hpφ t ht
  have hforward := hpres p hp hpf hpφ t ht
  have hinverse : Φ (-t) (Φ t p) = p := by
    rw [← Φ.map_add, neg_add_cancel, Flow.map_zero_apply]
  refine ⟨hforward.1, hforward.2.1, hforward.2.2.1, ?_, hinverse⟩
  constructor
  · intro hboundary
    have hback := hpres (Φ t p) (hforward.1 ▸ ht) hforward.2.1
      hforward.2.2.1 (-t) (by rw [hforward.1]; simpa only [add_neg_cancel_right] using hp)
    simpa only [hinverse] using hback.2.2.2 hboundary
  · exact hforward.2.2.2

end FsFltz
