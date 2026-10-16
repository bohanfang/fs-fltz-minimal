import FsFltz.Geometry.PotentialPathRoundedMotionFiber
import FsFltz.Geometry.MarkedHorizontalGluing

/-!
# Global lifts near the actual holomorphic full ribbons

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
matching truncations, lines 1010–1049, and assembly, lines 2127–2158.
The moving potential is retained in every frontier equation. Compactness
and local regular lifts construct the field; transport is a later consumer.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance pathGluingLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance pathGluingLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth
local instance pathGluingProdCharts : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
local instance pathGluingProdSmooth : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))

/-- Joint native smoothness of the literal moving affine potential. -/
theorem contMDiff_potentialPath_value_joint {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n =>
        potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1) := by
  rw [modelWithCornersSelf_prod]
  exact ((contMDiff_const.sub contMDiff_fst).mul
    (contMDiff_original_phi0.comp contMDiff_snd)).add
    (contMDiff_fst.mul ((contMDiff_potentialValue hφ).comp contMDiff_snd))

/-- Compactness of the entire truncated moving holomorphic fiber. -/
theorem isCompact_potentialPath_truncatedTotalSpace
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (R A : ℝ) (hA : 0 ≤ A) :
    IsCompact {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      W (I.alongCoefficientPath p.1) p.2 = (R : ℂ) ∧
      potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 ≤ A} := by
  have hbase := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
    ((isCompact_phi0_sublevel A hA).union
      (isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend A))
  have hψ := (contMDiff_potentialPath_value_joint hφ).continuous
  have hf := (contMDiff_coefficientPath_W_native_joint I).continuous
  have hclosed : IsClosed {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      W (I.alongCoefficientPath p.1) p.2 = (R : ℂ) ∧
      potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 ≤ A} :=
    (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_eq hf continuous_const).inter (isClosed_le hψ continuous_const))
  apply hbase.of_isClosed_subset hclosed
  intro p hp
  refine ⟨hp.1, ?_⟩
  by_cases h₀ : phi0 p.2 ≤ A
  · exact Or.inl h₀
  · right
    by_contra h₁
    have h₀' : A < realSquaredNorm p.2.1 / 2 := lt_of_not_ge h₀
    have h₁' : A < φ p.2.1 := lt_of_not_ge h₁
    have hpot := hp.2.2
    change (1 - p.1) * (realSquaredNorm p.2.1 / 2) + p.1 * φ p.2.1 ≤ A at hpot
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1.2) (sub_nonneg.mpr h₀'.le),
      mul_nonneg hp.1.1 (sub_nonneg.mpr h₁'.le)]

/-- Construct one smooth native parameter lift near the literal compact
holomorphic ribbon family, preserving the actual fiber equation throughout
an open neighborhood and the potential on an open boundary collar.
The constants precede the scale and every later truncation level. -/
theorem ToricInput.coefficientPath_potentialPath_exists_uniform_compact_horizontalField
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
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
      ∃ (O B : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          W (I.alongCoefficientPath p.1) p.2 = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 ≤ A} ⊆ O ∧
        IsOpen B ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          W (I.alongCoefficientPath p.1) p.2 = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 = A} ⊆ B ∧
        ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
          (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n))
            (ℝ × LGSpace n))) ∧
        (∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
          (fun q : ℝ × LGSpace n => (q.1, W (I.alongCoefficientPath q.1) q.2)) p (V p) = (1, 0)) ∧
        ∀ p ∈ O ∩ B, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × LGSpace n => potentialPath (fun u => realSquaredNorm u / 2) φ q.1 q.2.1) p (V p) = 0 := by
  obtain ⟨R₀, hR₀, hlocal⟩ := FsFltz.Geometry.ToricInput.coefficientPath_exists_local_fiber_horizontalField I
  obtain ⟨F, hF, B₁, hB₁, hmarked⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_potentialPath_exists_local_marked_horizontalField I
      hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, max (max 1 (Real.log R₀)) B₁, (zero_lt_one.trans_le (le_max_left _ _)).trans_le (le_max_left _ _), ?_⟩
  intro β hβ A hA
  have hR : R₀ ≤ Real.exp β := by
    have hlog : Real.log R₀ ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ)
    simpa only [Real.exp_log hR₀] using Real.exp_le_exp.mpr hlog
  let C : Set (ℝ × LGSpace n) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧
    W (I.alongCoefficientPath p.1) p.2 = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 ≤ A}
  let T : Set (ℝ × LGSpace n) := {p | potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 = A}
  let g : ℝ × LGSpace n → ℝ × ℂ := fun p => (p.1, W (I.alongCoefficientPath p.1) p.2)
  let ρ : ℝ × LGSpace n → ℝ := fun p => potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1
  have hC : IsCompact C := isCompact_potentialPath_truncatedTotalSpace
    I hφ hEnd1 hEnd hhom hc hlower hL hend (Real.exp β) A
      ((by positivity : (0 : ℝ) ≤ F ^ 2 * β ^ 2 / 2).trans hA)
  have hτ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × LGSpace n → ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hf : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => W (I.alongCoefficientPath p.1) p.2) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_coefficientPath_W_native_joint I
  have hρ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ := by
    exact contMDiff_potentialPath_value_joint hφ
  have hT : IsClosed T := isClosed_eq hρ.continuous continuous_const
  let D : (p : ℝ × LGSpace n) →
      TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p →L[ℝ] ℝ × ℂ :=
    fun p => mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ) g p
  let H : (p : ℝ × LGSpace n) →
      TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p →L[ℝ] ℝ × ℂ :=
    fun p => (ContinuousLinearMap.inl ℝ ℝ ℂ).comp
      (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ρ p)
  obtain ⟨O, B, V, hO, hCO, hB, hCB, hV, hD, hH⟩ :=
    exists_smooth_boundary_horizontal_lift_near_compact C hC T hT D H
      (fun _ => (1, 0)) (fun _ => 0) (by
        intro p hp
        exact hlocal (Real.exp β) hR p.1 hp.1 p.2 hp.2.1) (by
        intro p hp
        obtain ⟨P, Z, hP, hpP, hZ, heq⟩ :=
          hmarked β ((le_max_right _ _).trans hβ) p.1 hp.1.1 p.2 hp.1.2.1
            (by change F ^ 2 * β ^ 2 / 2 ≤ ρ p; rw [show ρ p = A from hp.2]; exact hA)
        refine ⟨P, Z, hP, hpP, hZ, ?_⟩
        intro q hq
        have hcomp := parameter_marked_horizontal_components
          (hτ.mdifferentiableAt (x := q) (by simp))
          (hf.mdifferentiableAt (x := q) (by simp))
          (hρ.mdifferentiableAt (x := q) (by simp)) (Z q) (heq q hq)
        refine ⟨hcomp.1, ?_⟩
        change ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ρ q) (Z q),
          (0 : ℂ)) = 0
        rw [hcomp.2]
        rfl)
  refine ⟨O, B, V, hO, hCO, hB, ?_, hV, hD, ?_⟩
  · intro p hp
    exact hCB ⟨⟨hp.1, hp.2.1, hp.2.2.le⟩, hp.2.2⟩
  · intro p hp
    exact congrArg Prod.fst (hH p hp)


end FsFltz.Geometry
