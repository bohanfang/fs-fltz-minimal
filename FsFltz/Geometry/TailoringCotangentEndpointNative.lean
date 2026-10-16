import FsFltz.Geometry.PotentialLiouville
import FsFltz.Geometry.RegularSublevelDomain
import FsFltz.Geometry.BoundaryOutwardAbsorptionMarking
import FsFltz.Target

/-!
# The native standard cotangent disk and its radial completion

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 92–108;
`geometric-part-fsf-proof.tex`, `prop:endpoint`, lines 1922–1959.
The disk, complete flow, and end map are constructed from the literal
canonical primitive on the existing quotient cotangent manifold.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance endpointCotangentCharts : ChartedSpace (Model (2 * n)) (Cotangent n) :=
  (cotangentManifold n).charts
local instance endpointCotangentSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (Cotangent n) :=
  (cotangentManifold n).smooth

/-- The canonical Liouville field is the actual momentum-radial vector. -/
theorem liouvilleVector_lambdaCanForm_radial (x : TangentCoordinates n) :
    (cotangentManifold n).liouvilleVector (lambdaCanForm n) (cotangentCover x) =
      cotangentCoverTangent x (0, x.2) := by
  apply (cotangentManifold n).liouvilleVector_eq _ _
    (nondegenerate_exteriorDerivative_lambdaCanForm _)
  intro v
  obtain ⟨q, rfl⟩ := (cotangentCoverTangent_bijective x).2 v
  rw [exteriorDerivative_lambdaCanForm_cotangentCover, lambdaCanForm_cotangentCover]
  simp

/-- The standard action preserves the angle and scales its literal momentum. -/
def cotangentRadialAction (t : ℝ) (x : Cotangent n) : Cotangent n :=
  (x.1, Real.exp t • x.2)

theorem contMDiff_cotangentRadialAction :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (2 * n)) ∞
      (fun p : ℝ × Cotangent n => cotangentRadialAction p.1 p.2) := by
  let cI := (torusModel n).prod 𝓘(ℝ, RealSpace n)
  have h : ContMDiff ((𝓘(ℝ, ℝ)).prod cI) cI ∞
      (fun p : ℝ × Cotangent n => (p.2.1, Real.exp p.1 • p.2.2)) :=
    (contMDiff_fst.comp contMDiff_snd).prodMk
      ((Real.contDiff_exp.contMDiff.comp contMDiff_fst).smul
        (contMDiff_snd.comp contMDiff_snd))
  exact (contMDiff_linearRechart_id (M := Cotangent n) (cotangentEuclideanEquiv n)).comp
    (h.comp (contMDiff_fst.prodMk
      ((contMDiff_linearRechart_id_symm (M := Cotangent n)
        (cotangentEuclideanEquiv n)).comp contMDiff_snd)))

theorem isMIntegralCurve_cotangentRadialAction (y : Cotangent n) :
    IsMIntegralCurve (fun t => cotangentRadialAction t y)
      ((cotangentManifold n).liouvilleVector (lambdaCanForm n)) := by
  obtain ⟨x, rfl⟩ := cotangentCover_surjective n y
  intro t
  let γ : ℝ → TangentCoordinates n := fun s => (x.1, Real.exp s • x.2)
  have hd := (hasDerivAt_const t x.1).prodMk ((Real.hasDerivAt_exp t).smul_const x.2)
  have hc := ((contMDiff_cotangentCover n).mdifferentiableAt (by simp)
    (x := γ t)).hasMFDerivAt.comp t
      (hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt)
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change cotangentCoverTangent (γ t) (r • ((0 : RealSpace n), Real.exp t • x.2)) =
    r • (cotangentManifold n).liouvilleVector (lambdaCanForm n) (cotangentCover (γ t))
  rw [map_smul, liouvilleVector_lambdaCanForm_radial]

/-- The standard canonical flow is defined smoothly in both real time directions. -/
def cotangentRadialCompleteFlow (n : ℕ) :
    CompleteLiouvilleFlow (cotangentManifold n)
      ((cotangentManifold n).liouvilleVector (lambdaCanForm n)) where
  flow :=
    { toFun := cotangentRadialAction
      cont' := contMDiff_cotangentRadialAction.continuous
      map_add' := by
        intro s t x
        simp [cotangentRadialAction, Real.exp_add, mul_smul]
      map_zero' := by
        intro x
        simp [cotangentRadialAction] }
  smooth_action := contMDiff_cotangentRadialAction
  solves := fun y => (isMIntegralCurve_iff_chart_solves (cotangentManifold n) _ _
    ((contMDiff_cotangentRadialAction.comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))).mp
        (isMIntegralCurve_cotangentRadialAction y)

/-- Completeness of the prescribed canonical cotangent primitive. -/
def cotangentCompletePrimitive (n : ℕ) :
    CompletePrimitive (cotangentManifold n) (lambdaCanForm n) where
  smooth_primitive := isSmoothForm_lambdaCanForm n
  symplectic := isSymplecticOn_exteriorDerivative_lambdaCanForm n
  smooth_field := isSmoothVectorField_liouvilleVector_lambdaCanForm n
  contraction := fun y => (cotangentManifold n).liouvilleVector_contraction _ y
    ((cotangentManifold n).liouvilleEquation_exists _ y
      (nondegenerate_exteriorDerivative_lambdaCanForm y))
  completeFlow := cotangentRadialCompleteFlow n

/-- The defining function uses the based Euclidean norm fixed by the target. -/
def cotangentDiskDefining (x : Cotangent n) : ℝ := realSquaredNorm x.2 - 1

theorem contMDiff_cotangentDiskDefining :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (cotangentDiskDefining (n := n)) := by
  unfold cotangentDiskDefining realSquaredNorm
  exact (ContMDiff.sum (fun j _ => (contMDiff_cotangentMomentumCoordinate j).pow 2)).sub
    contMDiff_const

theorem realSquaredNorm_smul (a : ℝ) (u : RealSpace n) :
    realSquaredNorm (a • u) = a ^ 2 * realSquaredNorm u := by
  simp only [realSquaredNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem cotangentDiskDefining_radialAction (t : ℝ) (x : Cotangent n) :
    cotangentDiskDefining (cotangentRadialAction t x) =
      Real.exp (2 * t) * realSquaredNorm x.2 - 1 := by
  simp only [cotangentDiskDefining, cotangentRadialAction, realSquaredNorm_smul]
  rw [← Real.exp_nat_mul]
  norm_num

theorem scalarDerivative_cotangentDiskDefining (x : Cotangent n) :
    (cotangentManifold n).scalarDerivative cotangentDiskDefining x
      ((cotangentManifold n).liouvilleVector (lambdaCanForm n) x) =
        2 * realSquaredNorm x.2 := by
  have hd := (cotangentRadialCompleteFlow n).hasDerivAt_scalar_orbit
    cotangentDiskDefining contMDiff_cotangentDiskDefining x 0
  have he := (((Real.hasDerivAt_exp (2 * (0 : ℝ))).comp 0
    ((hasDerivAt_id 0).const_mul 2)).mul_const (realSquaredNorm x.2)).sub_const 1
  simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at he
  have he' : HasDerivAt
      (fun t => cotangentDiskDefining (cotangentRadialAction t x))
      (2 * realSquaredNorm x.2) 0 := by
    convert he using 1
    funext t
    exact cotangentDiskDefining_radialAction t x
  have h := hd.unique he'
  have hzero : (cotangentRadialCompleteFlow n).flow 0 x = x :=
    (cotangentRadialCompleteFlow n).flow.map_zero_apply x
  rw [hzero] at h
  exact h

theorem cotangentDiskDefining_outward (x : Cotangent n)
    (hx : cotangentDiskDefining x = 0) :
    0 < (cotangentManifold n).scalarDerivative cotangentDiskDefining x
      ((cotangentManifold n).liouvilleVector (lambdaCanForm n) x) := by
  rw [scalarDerivative_cotangentDiskDefining]
  have h : realSquaredNorm x.2 = 1 := sub_eq_zero.mp hx
  rw [h]
  norm_num

theorem isCompact_cotangentDisk : IsCompact (cotangentDisk (n := n)) := by
  have he : cotangentDisk (n := n) = Prod.swap ''
      {y : LGSpace n | phi0 y ≤ (1 / 2 : ℝ)} := by
    ext x
    simp only [mem_image, cotangentDisk, mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨x.swap, by change realSquaredNorm x.2 / 2 ≤ 1 / 2; linarith, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      change realSquaredNorm y.1 / 2 ≤ 1 / 2 at hy
      change realSquaredNorm y.1 ≤ 1
      linarith
  rw [he]
  exact (isCompact_phi0_sublevel (1 / 2) (by norm_num)).image continuous_swap

/-- The literal unit Euclidean disk with its canonical primitive. -/
def standardCotangentDisk (n : ℕ) : LiouvilleDomain (2 * n) :=
  regularSublevelLiouvilleDomain (cotangentManifold n) cotangentDiskDefining
    contMDiff_cotangentDiskDefining
    (by
      change IsCompact {x : Cotangent n | realSquaredNorm x.2 - 1 ≤ 0}
      simpa only [sub_nonpos, cotangentDisk] using (isCompact_cotangentDisk (n := n)))
    (lambdaCanForm n) (isSmoothForm_lambdaCanForm n)
    (isSymplecticOn_exteriorDerivative_lambdaCanForm n) cotangentDiskDefining_outward

@[simp] theorem standardCotangentDisk_carrier (n : ℕ) :
    (standardCotangentDisk n).domain.carrier = cotangentDisk := by
  ext x
  change (realSquaredNorm x.2 - 1 ≤ 0) ↔ realSquaredNorm x.2 ≤ 1
  exact sub_nonpos

@[simp] theorem standardCotangentDisk_primitive (n : ℕ) :
    (standardCotangentDisk n).liouville.primitive = lambdaCanForm n := rfl

theorem standardCotangentDisk_frontier (n : ℕ) :
    frontier (standardCotangentDisk n).domain.carrier = cosphere := by
  unfold standardCotangentDisk
  rw [regularSublevelLiouvilleDomain_frontier]
  ext x
  exact sub_eq_zero

theorem cotangentDisk_negative_absorption (x : Cotangent n) :
    ∃ T : ℝ, 0 ≤ T ∧
      cotangentDiskDefining ((cotangentRadialCompleteFlow n).flow (-T) x) ≤ 0 := by
  let T := max 0 (Real.log (realSquaredNorm x.2 + 1))
  have hr : 0 ≤ realSquaredNorm x.2 := by
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hT : 0 ≤ T := le_max_left _ _
  have hlog : Real.log (realSquaredNorm x.2 + 1) ≤ T := le_max_right _ _
  have he : realSquaredNorm x.2 + 1 ≤ Real.exp T := by
    rw [← Real.exp_log (by linarith : 0 < realSquaredNorm x.2 + 1)]
    exact Real.exp_le_exp.mpr hlog
  have he2 : realSquaredNorm x.2 ≤ Real.exp (2 * T) := by
    have h := Real.exp_le_exp.mpr (show T ≤ 2 * T by linarith)
    linarith
  refine ⟨T, hT, ?_⟩
  change cotangentDiskDefining (cotangentRadialAction (-T) x) ≤ 0
  rw [cotangentDiskDefining_radialAction]
  have hp := mul_le_mul_of_nonneg_left he2 (Real.exp_pos (2 * -T)).le
  have hc : Real.exp (2 * -T) * Real.exp (2 * T) = 1 := by
    rw [← Real.exp_add]
    rw [show 2 * -T + 2 * T = 0 by ring, Real.exp_zero]
  rw [hc] at hp
  linarith

/-- The disk's actual completion is the entire canonical cotangent ambient. -/
def standardCotangentCompletion (n : ℕ) : Completion (standardCotangentDisk n) :=
  BoundaryOutwardAbsorptionMarking.completionOfBoundaryOutwardAbsorption
    (standardCotangentDisk n) (cotangentCompletePrimitive n)
    cotangentDiskDefining contMDiff_cotangentDiskDefining
    (by rw [standardCotangentDisk_frontier]; ext x; exact sub_eq_zero.symm)
    cotangentDiskDefining_outward rfl cotangentDisk_negative_absorption

@[simp] theorem standardCotangentCompletion_inclusion (n : ℕ) (x : Cotangent n) :
    (standardCotangentCompletion n).inclusion.map x = x := rfl

@[simp] theorem standardCotangentCompletion_end (n : ℕ)
    (x : (standardCotangentDisk n).domain.boundary.Point) (r : ℝ) :
    (standardCotangentCompletion n).endMap (x, r) =
      cotangentRadialAction r ((standardCotangentDisk n).domain.boundaryInclusion.map x) := rfl

theorem standardCotangentDisk_boundary_range (n : ℕ) :
    range (standardCotangentDisk n).domain.boundaryInclusion.map = cosphere :=
  (standardCotangentDisk n).domain.boundary_range.trans (standardCotangentDisk_frontier n)

end FsFltz.Geometry
