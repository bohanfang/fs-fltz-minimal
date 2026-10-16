import FsFltz.Geometry.TailoringRoundedMarkedLift
import FsFltz.Geometry.MarkedPairTransport

/-!
# One actual flow transporting the rounded tailoring pair

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and the marked deformation, lines 1239–1326. The same constructed smooth
flow transports the whole rounded domain, its boundary, the entire ribbon,
and its frontier throughout the full parameter interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set

namespace FsFltz
open Geometry
variable {n : ℕ}

local instance roundedTransportLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance roundedTransportLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
local instance roundedTransportProdCharts : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
local instance roundedTransportProdSmooth : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))

/-- Simultaneous transport of the literal rounded pair by one constructed
smooth flow. Local compatibility and confinement are proved producers,
not additional assumptions on the finite toric input. -/
theorem tailoringFamily_exists_uniform_rounded_pair_transport
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
    ∃ F : ℝ, 0 < F ∧ ∀ D : ℝ, F < D →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ Φ : Flow ℝ (ℝ × LGSpace n),
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n)))
          𝓘(ℝ, ℝ × Model (2 * n)) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => Φ p.1 p.2) ∧
        (∀ p : ℝ × LGSpace n, p.1 ∈ Icc (0 : ℝ) 1 →
          p.2 ∈ tailoringRoundedDomain I φ β p.1 R (D ^ 2 * β ^ 2 / 2) m →
          ∀ t : ℝ, p.1 + t ∈ Icc (0 : ℝ) 1 →
            (Φ t p).1 = p.1 + t ∧
            (Φ t p).2 ∈ tailoringRoundedDomain I φ β (Φ t p).1 R (D ^ 2 * β ^ 2 / 2) m ∧
            (tailoringRoundedDefiningFunction I φ β (Φ t p).1 R
              (D ^ 2 * β ^ 2 / 2) m (Φ t p).2 = 0 ↔
              tailoringRoundedDefiningFunction I φ β p.1 R (D ^ 2 * β ^ 2 / 2) m p.2 = 0)) ∧
        (∀ p : ℝ × LGSpace n, p.1 ∈ Icc (0 : ℝ) 1 →
          tailoringFamily I β p.1 p.2 = 1 → φ p.2.1 ≤ Aminus →
          ∀ t : ℝ, p.1 + t ∈ Icc (0 : ℝ) 1 →
            (Φ t p).1 = p.1 + t ∧ tailoringFamily I β (Φ t p).1 (Φ t p).2 = 1 ∧
            φ (Φ t p).2.1 ≤ Aminus ∧ (φ (Φ t p).2.1 = Aminus ↔ φ p.2.1 = Aminus)) := by
  obtain ⟨F, hF, hfield⟩ := tailoringFamily_exists_uniform_rounded_marked_horizontalField
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, ?_⟩
  intro D hD
  obtain ⟨β₀, hβ₀, hfield⟩ := hfield D hD
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ
  have hfield := hfield β hβ
  intro R hR Aminus hlo hhi
  obtain ⟨δ, hδ, hgap, hfield⟩ := hfield R hR Aminus hlo hhi
  refine ⟨δ, hδ, hgap, ?_⟩
  intro m hm hmd
  obtain ⟨O, B, Rb, J, V, hO, hCO, hB, hCB, hRb, hCR, hJ, hCJ,
    hV, hparam, hboundary, hribbon, hfrontier⟩ := hfield m hm hmd
  have hτ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × LGSpace n → ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hq : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => tailoringRoundedDefiningFunction I φ β p.1 R
        (D ^ 2 * β ^ 2 / 2) m p.2) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_tailoringRoundedDefiningFunction_joint I hφ β R (D ^ 2 * β ^ 2 / 2) m
  have hφj : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => φ p.2.1) := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiff_potentialValue hφ).comp contMDiff_snd
  have hf : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => tailoringFamily I β p.1 p.2) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_tailoringFamily_native_joint I β
  have hinc : ∀ p : ℝ × LGSpace n, p.1 ∈ Icc (0 : ℝ) 1 →
      tailoringFamily I β p.1 p.2 = 1 → φ p.2.1 ≤ Aminus →
      tailoringRoundedDefiningFunction I φ β p.1 R (D ^ 2 * β ^ 2 / 2) m p.2 ≤ 0 := by
    intro p _hp hpf hpφ
    obtain ⟨U, _hU, hpU, hagree⟩ := tailoringRoundedDefiningFunction_exists_unrounded_germ
      I hφ β R (D ^ 2 * β ^ 2 / 2) Aminus m hm (by linarith) p.1 p.2 hpf hpφ
    rw [hagree p hpU, hpf, Complex.normSq_one, sub_self, mul_zero]
  exact exists_supported_pairTransport_near_compact Prod.fst
    (fun p : ℝ × LGSpace n => tailoringRoundedDefiningFunction I φ β p.1 R
      (D ^ 2 * β ^ 2 / 2) m p.2)
    (fun p : ℝ × LGSpace n => φ p.2.1)
    (fun p : ℝ × LGSpace n => tailoringFamily I β p.1 p.2) 1 Aminus
    hτ hq hφj hf (isCompact_tailoringRoundedDomain_totalSpace I hφ hEnd1 hEnd hhom
      hc hlower hL hend β R (D ^ 2 * β ^ 2 / 2) m) hinc
    O B Rb J hO hB hRb hJ hCO hCB hCR hCJ V hV.contMDiffOn
    hparam hboundary hribbon (fun p hp => hfrontier p ⟨hp.1.1, hp.2⟩)

end FsFltz
