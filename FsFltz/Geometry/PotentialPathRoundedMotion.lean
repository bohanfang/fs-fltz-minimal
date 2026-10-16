import FsFltz.Geometry.PotentialPathRoundedOutward
import FsFltz.Geometry.MarkedLevelHorizontalField
import FsFltz.Geometry.PotentialFiberCompleteFlowNative

/-!
# Actual scalar boundary lifts along the holomorphic path

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
the coefficient choice, lines 1315–1326, and assembly, lines 2127–2158.
The original specification's `thm:target` and `sec:lean` require actual
compact families; scalar lifts alone do not furnish simultaneous full-ribbon
transport or its completion markings. Here regularity, local motions, and
local horizontal fields are constructed from finite analytic bounds.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance roundedMotionLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance roundedMotionLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- Compactness of the actual scalar sublevel family with moving potential.
The affine path sublevel lies in the union of its two endpoint sublevels.
No preassigned common compact domain is assumed. -/
theorem isCompact_potentialPath_rounded_totalSpace
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (R A : ℝ) (hA : 0 ≤ A) (m : RoundingChoice) :
    IsCompact {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      potentialPath_roundedDefiningFunction I φ R A m p ≤ 0} := by
  have hbase := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
    ((isCompact_phi0_sublevel A hA).union
      (isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend A))
  have hq := (contMDiff_potentialPath_roundedDefiningFunction_joint I hφ R A m).continuous
  have hclosed : IsClosed {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      potentialPath_roundedDefiningFunction I φ R A m p ≤ 0} :=
    (isClosed_Icc.preimage continuous_fst).inter (isClosed_le hq continuous_const)
  apply hbase.of_isClosed_subset hclosed
  intro p hp
  refine ⟨hp.1, ?_⟩
  have hpot : potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 ≤ A := by
    have h := (le_max_left
      (potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 - A)
      (Complex.normSq (W (I.alongCoefficientPath p.1) p.2) - R ^ 2)).trans
        ((m.profile.lower _).trans hp.2)
    exact sub_nonpos.mp h
  by_cases h₀ : phi0 p.2 ≤ A
  · exact Or.inl h₀
  · right
    by_contra h₁
    have h₀' : A < realSquaredNorm p.2.1 / 2 := lt_of_not_ge h₀
    have h₁' : A < φ p.2.1 := lt_of_not_ge h₁
    change (1 - p.1) * (realSquaredNorm p.2.1 / 2) + p.1 * φ p.2.1 ≤ A at hpot
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1.2) (sub_nonneg.mpr h₀'.le),
      mul_nonneg hp.1.1 (sub_nonneg.mpr h₁'.le)]

/-- A single width and coefficient threshold construct actual smooth
parameter motions and horizontal fields near every boundary point of
the literal holomorphic rounded path, including both endpoints. -/
theorem ToricInput.coefficientPath_potentialPath_rounded_boundary_lifts
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    let hφE := hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
    ∃ A₀ R₀ : ℝ, 0 < A₀ ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ Kstar : ℝ, 0 < Kstar ∧
      coefficientPotentialPathThreshold I hφE hc hlower R ≤ Kstar ∧
      ∀ A : ℝ, 2 * A₀ ≤ A → ∀ Aminus : ℝ, Aminus < A →
      ∃ δ : ℝ, 0 < δ ∧ δ < A - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      potentialPath_roundedDefiningFunction I φ R A m (t, y) = 0 →
      letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
        inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
      letI : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
        rw [modelWithCornersSelf_prod]
        exact inferInstanceAs
          (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
      (∃ (O : Set (ℝ × (ℝ × LGSpace n))) (Ψ : ℝ × (ℝ × LGSpace n) → ℝ × LGSpace n),
        IsOpen O ∧ (0, (t, y)) ∈ O ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n)))
          𝓘(ℝ, ℝ × Model (2 * n)) ∞ Ψ O ∧
        (∀ p, (0, p) ∈ O → Ψ (0, p) = p) ∧
        ∀ p ∈ O, (Ψ p).1 = p.2.1 + p.1 ∧
          potentialPath_roundedDefiningFunction I φ R A m (Ψ p) =
            potentialPath_roundedDefiningFunction I φ R A m p.2) ∧
      (∃ (O : Set (ℝ × LGSpace n))
          (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧ (t, y) ∈ O ∧
        ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n)) (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) O ∧
        ∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℝ)
          (fun q : ℝ × LGSpace n =>
            (q.1, potentialPath_roundedDefiningFunction I φ R A m q)) p (V p) = (1, 0)) := by
  obtain ⟨A₀, R₀, hA₀, hR₀, hout⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_potentialPath_rounded_outward
      I hφ hc hlower hupper hEnd hhom hL hend
  refine ⟨A₀, R₀, hA₀, hR₀, ?_⟩
  intro R hR
  obtain ⟨Kstar, hKstar, hthreshold, hout⟩ := hout R hR
  refine ⟨Kstar, hKstar, hthreshold, ?_⟩
  intro A hA Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout A hA Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd t ht y hy
  let D := differentialCovector (lgManifold n)
    (fun z => potentialPath_roundedDefiningFunction I φ R A m (t, z)) y
  let Z := (lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
    (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t))
    (W (I.alongCoefficientPath t)) Kstar) y
  have hDZ : D Z ≠ 0 := (hout m hm hmd Kstar le_rfl t ht y hy.ge).ne'
  have hsurj : Function.Surjective (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (fun z => potentialPath_roundedDefiningFunction I φ R A m (t, z)) y) := by
    change Function.Surjective D
    intro a
    refine ⟨(a / D Z) • Z, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ a hDZ
  have hq := contMDiff_potentialPath_roundedDefiningFunction_joint I hφ R A m
  exact ⟨exists_parameter_level_local_motion hq hsurj,
    exists_parameter_level_horizontalField hq hsurj⟩

end FsFltz.Geometry
