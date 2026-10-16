import FsFltz.Geometry.PotentialAmbientPath
import FsFltz.Geometry.MarkedLevelFamily
import FsFltz.Analysis.OriginalRoundedBoundary

/-!
# Actual local motions of the original rounded boundary at the path start

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 909–930,
and `lem:markedfamily`, lines 975–1009; `geoemtric-part-fsf.tex`,
`def:rounding`, lines 309–326. The supplied arbitrary profile is retained
in the literal moving equation. The proved original outward derivative
gives its actual spatial regularity at s=0, and the native parameter-level
normal form gives a smooth local motion preserving that equation.

This producer covers neighborhoods of the initial parameter only.
Regularity over the whole path, simultaneous ribbon compatibility, and
compact gluing into a global marked family are separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance roundedPathRealContMDiffMul : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ where
  contMDiff_mul := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun _ _ => contDiff_mul.contDiffOn⟩

/-- Joint smoothness of the literal coefficient-path polynomial on the
actual quotient with the native fixed-dimensional chart model. -/
theorem contMDiff_coefficientPath_W_native_joint (I : ToricInput n) :
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => W (I.alongCoefficientPath p.1) p.2) := by
  have hmul {f g : ℝ × LGSpace n → ℂ}
      (hf : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞ f)
      (hg : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞ g) :
      ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞ (fun p => f p * g p) :=
    (show ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2) from
      contDiff_fst.mul contDiff_snd).contMDiff.comp (hf.prodMk_space hg)
  have hW : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => W (I.alongCoefficientPath p.1) p.2) := by
    have hsum := ContMDiff.sum (t := Finset.univ)
      (fun (v : {v : Lattice n // v ∈ I.vertices}) _ =>
        hmul ((coefficientPath_contDiff I v).contMDiff.comp contMDiff_fst)
        ((contMDiff_monomial 1 v.val).comp contMDiff_snd))
    convert hsum using 1
    ext p
    simp only [Function.comp_apply, W, ToricInput.alongCoefficientPath, monomial, one_mul, mul_assoc]
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hp : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
      (𝓘(ℝ, ℝ).prod (lgModel n)) ∞ (fun p : ℝ × LGSpace n => p) :=
    contMDiff_fst.prodMk
      ((contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n)).comp
        contMDiff_snd)
  exact hW.comp hp

/-- The literal moving rounded scalar uses the retained supplied profile
and the prescribed coefficient and potential paths at the same parameter. -/
def potentialPath_roundedDefiningFunction (I : ToricInput n) (φ : RealSpace n → ℝ)
    (R A : ℝ) (m : RoundingChoice) (p : ℝ × LGSpace n) : ℝ :=
  m.profile.toFun (potentialPath (fun x => realSquaredNorm x / 2) φ p.1 p.2.1 - A,
    Complex.normSq (W (I.alongCoefficientPath p.1) p.2) - R ^ 2)

@[simp]
theorem potentialPath_roundedDefiningFunction_zero (I : ToricInput n)
    (φ : RealSpace n → ℝ) (R A : ℝ) (m : RoundingChoice) (y : LGSpace n) :
    potentialPath_roundedDefiningFunction I φ R A m (0, y) =
      roundedDefiningFunction I R A m y := by
  simp [potentialPath_roundedDefiningFunction, potentialPath, roundedDefiningFunction, phi0]

/-- The actual rounded scalar is jointly smooth in parameter and space;
it extends smoothly across the initial parameter endpoint. -/
theorem contMDiff_potentialPath_roundedDefiningFunction_joint (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (R A : ℝ) (m : RoundingChoice) :
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞
      (potentialPath_roundedDefiningFunction I φ R A m) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hpath : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => potentialPath (fun x => realSquaredNorm x / 2) φ p.1 p.2.1) :=
    ((contMDiff_const.sub contMDiff_fst).mul
      (contMDiff_original_phi0.comp contMDiff_snd)).add
      (contMDiff_fst.mul ((contMDiff_potentialValue hφ).comp contMDiff_snd))
  have habs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => Complex.normSq (W (I.alongCoefficientPath p.1) p.2)) := by
    simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
      (contDiff_norm_sq ℝ).contMDiff.comp (contMDiff_coefficientPath_W_native_joint I)
  exact m.profile.smooth.contMDiff.comp
    ((hpath.sub contMDiff_const).prodMk_space (habs.sub contMDiff_const))

/-- Every boundary point of every supplied admissible initial rounded
domain admits an actual jointly smooth local motion along the literal
coefficient/potential rounded equation. No all-path regularity is assumed
or asserted; the motion is constructed near the initial parameter. -/
theorem originalRoundedBoundary_exists_initial_potentialPath_local_motion
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {Aamb R Afib K Aminus A : ℝ}
    (hamb : AmbientEndBound I Aamb) (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hm : GeometricAdmissibleRounding I R K Aminus A m)
    (y : LGSpace n) (hy : roundedDefiningFunction I R A m y = 0) :
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
    ∃ (O : Set (ℝ × (ℝ × LGSpace n))) (Ψ : ℝ × (ℝ × LGSpace n) → ℝ × LGSpace n),
      IsOpen O ∧ (0, (0, y)) ∈ O ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n)))
        𝓘(ℝ, ℝ × Model (2 * n)) ∞ Ψ O ∧
      (∀ p, (0, p) ∈ O → Ψ (0, p) = p) ∧
      ∀ p ∈ O, (Ψ p).1 = p.2.1 + p.1 ∧
        potentialPath_roundedDefiningFunction I φ R A m (Ψ p) =
          potentialPath_roundedDefiningFunction I φ R A m p.2 := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  let : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
  have hpos := differentialCovector_roundedDefiningFunction_originalLiouville_pos
    I hamb hR hset hK hfib hlevels m hm y hy
  have hslice : (fun z : LGSpace n => potentialPath_roundedDefiningFunction I φ R A m (0, z)) =
      roundedDefiningFunction I R A m := funext (potentialPath_roundedDefiningFunction_zero I φ R A m)
  have hreg : Function.Surjective (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (fun z : LGSpace n => potentialPath_roundedDefiningFunction I φ R A m (0, z)) y) := by
    rw [hslice]
    let D := differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y
    let Z := (lgManifold n).liouvilleVector (lambdaKForm I K) y
    have hDZ : D Z ≠ 0 := hpos.ne'
    change Function.Surjective D
    intro a
    refine ⟨(a / D Z) • Z, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ a hDZ
  exact exists_parameter_level_local_motion
    (contMDiff_potentialPath_roundedDefiningFunction_joint I hφ R A m) hreg

end FsFltz.Geometry
