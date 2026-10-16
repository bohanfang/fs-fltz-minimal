import FsFltz.Geometry.TailoringCotangentEndpointRetained
import FsFltz.Geometry.PotentialLogarithmicGrading
import FsFltz.Geometry.FixedComplexMaslov
import FsFltz.Geometry.MaslovClassPullback
import FsFltz.Geometry.TargetGrading

/-!
# Grading of the retained Legendre endpoint

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 2075–2088.
The potential and Legendre diffeomorphism are the same selected analytic
witnesses retained by the finite-input hitting construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- Positive pointwise ratios permit straight interpolation of actual
smooth sections in one fixed canonical square. The ratio need not be
supplied as a smooth function: both sections already are smooth. -/
theorem MaslovRepresentative.homotopic_of_positive_ratio {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s r : MaslovRepresentative M eta) (hJ : r.J = s.J)
    (hr : ∀ x, ∃ a : ℝ, 0 < a ∧ r.tensor x = (a : ℂ) • s.tensor x) :
    MaslovHomotopic s r := by
  let T : ℝ → M.Point → SquaredCanonicalTensor n :=
    fun t x => ((1 - t : ℝ) : ℂ) • s.tensor x + (t : ℂ) • r.tensor x
  have hc (t : ℝ) (x : M.Point) : IsSquaredCanonicalTensor (s.J x) (T t x) := by
    apply (squaredCanonicalSubmodule (s.J x)).add_mem
    · exact (squaredCanonicalSubmodule (s.J x)).smul_mem _ (s.canonical x)
    · apply (squaredCanonicalSubmodule (s.J x)).smul_mem
      rw [← hJ]
      exact r.canonical x
  have hn (t : ℝ) (ht : t ∈ parameterInterval) (x : M.Point) : T t x ≠ 0 := by
    obtain ⟨a, ha, he⟩ := hr x
    have hp : 0 < (1 - t) + t * a := by
      by_cases hz : t = 0
      · simp [hz]
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
        exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos htpos ha)
    have hf : T t x = (((1 - t) + t * a : ℝ) : ℂ) • s.tensor x := by
      ext v
      simp [T, he, smul_eq_mul]
      ring
    rw [hf]
    exact smul_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne') (s.nowhereZero x)
  have hs (a : M.Point) : SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => squaredTensorInChart M a (T p.1) p.2) := by
    let V := (chartAt (Model (2 * n)) a).target
    let U : Set (ℝ × Model (2 * n)) := univ ×ˢ V
    have hss : ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      squaredTensorInChart M a s.tensor p.2) U :=
      (s.smooth a).comp contDiff_snd.contDiffOn (fun _ h => h.2)
    have hrs : ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      squaredTensorInChart M a r.tensor p.2) U :=
      (r.smooth a).comp contDiff_snd.contDiffOn (fun _ h => h.2)
    refine ⟨U, isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target,
      fun p hp => ⟨mem_univ _, hp.2⟩, ?_⟩
    have htime : ContDiff ℝ ∞ (fun p : ℝ × Model (2 * n) => (p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    have h := (((contDiff_const (c := (1 : ℂ))).sub htime).contDiffOn.smul hss).add
      (htime.contDiffOn.smul hrs)
    apply h.congr
    intro p hp
    ext v
    simp [T, squaredTensorInChart, smul_eq_mul]
  exact ⟨{
    family := {
      J := fun _ => s.J
      tensor := T
      compatible := fun _ _ => s.compatible
      canonical := fun t _ => hc t
      nowhereZero := hn
      smoothJ := fun a => SmoothNearInterval.constant
        (chartAt (Model (2 * n)) a).open_target (s.compatible.1 a)
      smoothSection := hs }
    sourceJ := rfl
    targetJ := hJ.symm
    sourceSection := by funext x; ext v; simp [T, smul_eq_mul]
    targetSection := by funext x; ext v; simp [T, smul_eq_mul] }⟩

end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- The actual prescribed logarithmic representative for the selected
zero-coefficient potential primitive. -/
def RetainedLegendrePotential.nativeMaslov {φEnd φ : RealSpace n → ℝ}
    (D : RetainedLegendrePotential φEnd φ) (I : ToricInput n) :
    MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) where
  J := logarithmicAlmostComplexField n
  tensor := logarithmicSquaredVolumeTensor n
  compatible := by
    have h := (logarithmicPotentialMaslovRepresentative I D.smooth D.lower_pos
      D.hessian_lower (K := 0) le_rfl).compatible
    change IsCompatibleAlmostComplex (lgManifold n)
      ((lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (W I) 0)) (logarithmicAlmostComplexField n) at h
    simpa [SmoothManifold.rankTwoPrimitive] using h
  canonical := logarithmicSquaredVolumeTensor_canonical
  smooth := isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor n
  nowhereZero := logarithmicSquaredVolumeTensor_ne_zero

/-- The retained Legendre map uses the actual selected global gradient. -/
def RetainedLegendrePotential.legendre {φEnd φ : RealSpace n → ℝ}
    (D : RetainedLegendrePotential φEnd φ) :
    (lgManifold n).SmoothEquiv (cotangentManifold n) :=
  legendreDiffeomorph D.gradient
    (by rw [show (D.gradient : RealSpace n → RealSpace n) = coordinateGradient φ
      from funext D.gradient_eq]; exact contDiff_coordinateGradient D.smooth)
    D.inverse_smooth

theorem RetainedLegendrePotential.legendre_primitive {φEnd φ : RealSpace n → ℝ}
    (D : RetainedLegendrePotential φEnd φ) :
    (lgManifold n).pullback (cotangentManifold n) D.legendre (lambdaCanForm n) =
      lambdaPotentialForm φ := by
  have he : (D.legendre : LGSpace n → Cotangent n) = legendreMap (coordinateGradient φ) := by
    funext y
    simp [RetainedLegendrePotential.legendre, legendreMap, D.gradient_eq]
  rw [he]
  exact pullback_lambdaCanForm_legendreMap D.smooth

/-- The actual cotangent datum pulled through that same Legendre map. -/
def RetainedLegendrePotential.legendreMaslov {φEnd φ : RealSpace n → ℝ}
    (D : RetainedLegendrePotential φEnd φ) :
    MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) :=
  pullbackCotangentMaslovRepresentative (lgManifold n) (lambdaPotentialForm φ)
    D.legendre D.legendre_primitive

end FsFltz
