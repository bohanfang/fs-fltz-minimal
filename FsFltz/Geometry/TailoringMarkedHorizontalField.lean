import FsFltz.Geometry.TailoringMarkedLevelFamily
import FsFltz.Geometry.MarkedLevelHorizontalField

/-!
# Native horizontal lifts of the actual tailoring equations

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009.
Native Poisson regularity and the proved intrinsic outward derivative construct
local tangent fields solving the actual fiber equations, with the potential
coordinate retained near every sufficiently large truncation boundary.
These fields feed simultaneous partition-of-unity gluing on the compact
ribbon total space; they do not assume a lift or a bundle trivialization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- Actual local horizontal lifts of every full tailored fiber, uniformly
for all sufficiently large scales. The affine derivative equation holds
on an open real neighborhood, including beyond interval endpoints. -/
theorem tailoringFamily_exists_uniform_local_fiber_horizontalField
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, tailoringFamily I β s y = 1 →
      letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      letI : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
      letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
        inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
      letI : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
        rw [modelWithCornersSelf_prod]
        exact inferInstanceAs
          (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
      ∃ (O : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧ (s, y) ∈ O ∧
        ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n))
          (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n))
            (ℝ × LGSpace n))) O ∧
        ∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × (ℂ))
          (fun q : ℝ × LGSpace n => (q.1, tailoringFamily I β q.1 q.2)) p (V p) = (1, 0) := by
  obtain ⟨_d, _hd, _R, _hR, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨Bπ, hBπ, ?_⟩
  intro β hβ s hs y hy
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  let : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
  have hpair := (hπ β hβ s hs y
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y)).2.2
      (by simp only [hy, norm_one, le_refl])
  have hreg := (lgManifold n).complexDifferential_surjective_of_planePairing_ne_zero
    (lambdaPotentialForm φ) (tailoringFamily I β s) y
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) hpair.ne'
  exact exists_parameter_level_horizontalField (contMDiff_tailoringFamily_native_joint I β) hreg

/-- Actual local horizontal lifts preserving both the fiber equation and
the potential coordinate throughout an open neighborhood of each point on
the sufficiently large whole-fiber end. Rank-one ends may be empty. -/
theorem tailoringFamily_exists_uniform_local_marked_fiber_horizontalField
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
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, tailoringFamily I β s y = 1 → F ^ 2 * β ^ 2 / 2 ≤ φ y.1 →
      letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      letI : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
      letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
        inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
      letI : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
        rw [modelWithCornersSelf_prod]
        exact inferInstanceAs
          (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
      ∃ (O : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧ (s, y) ∈ O ∧
        ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n))
          (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n))
            (ℝ × LGSpace n))) O ∧
        ∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × (ℂ × ℝ))
          (fun q : ℝ × LGSpace n => (q.1, (tailoringFamily I β q.1 q.2, φ q.2.1))) p (V p) = (1, 0) := by
  obtain ⟨F, hF, Bfull, hBfull, hfull⟩ := tailoringFamily_exists_uniform_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨_d, _hd, _R, _hR, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨F, hF, max Bfull Bπ, hBfull.trans_le (le_max_left _ _), ?_⟩
  intro β hβ s hs y hy hlevel
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  let : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
  obtain ⟨N, j, _P, himage, hlevels⟩ := hfull β ((le_max_left _ _).trans hβ) s hs
  let hpos := (hlevels (F ^ 2 * β ^ 2 / 2) le_rfl).choose
  have hymem : y ∈ range j.map := by rw [himage]; exact hy
  obtain ⟨x, rfl⟩ := hymem
  have hj : ∀ z, tailoringFamily I β s (j.map z) = 1 := by
    intro z
    have hm : j.map z ∈ range j.map := ⟨z, rfl⟩
    rwa [himage] at hm
  have hpair := (hπ β ((le_max_right _ _).trans hβ) s hs (j.map x)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map x))).2.2
      (by simp only [hy, norm_one, le_refl])
  have hreg := (lgManifold n).complexDifferential_surjective_of_planePairing_ne_zero
    (lambdaPotentialForm φ) (tailoringFamily I β s) (j.map x)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map x)) hpair.ne'
  have hmarked := surjective_markedLevel_of_fiber_tangent (lgManifold n) N
    (tailoringFamily I β s) (fun z => φ z.1) (contMDiff_tailoringFamily_lgManifold I β s)
    (contMDiff_potentialValue hφ) j 1 hj x hreg
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x)
    (hpos x hlevel).ne'
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ × ℝ) ∞
      (fun p : ℝ × LGSpace n => (tailoringFamily I β p.1 p.2, φ p.2.1)) :=
    (contMDiff_tailoringFamily_native_joint I β).prodMk_space
      ((contMDiff_potentialValue hφ).comp contMDiff_snd)
  exact exists_parameter_level_horizontalField (E := Model (2 * n)) (F := ℂ × ℝ)
    (M := LGSpace n) (a := (s, j.map x))
    (f := fun p => (tailoringFamily I β p.1 p.2, φ p.2.1)) hsmooth hmarked

end FsFltz
