import FsFltz.Geometry.FormScalarDerivative
import FsFltz.Geometry.SmoothLiouville
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# The radial Liouville equation from a prescribed cylinder primitive

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`sec:lean`, lines 805–821. Radius increases outward, so the prescribed
primitive is `exp(r) α` and the field is `+∂r`. The finite intrinsic
collar uses inward time `t`, related by `r = -t`.

All maps land in the given raw ambient manifold. The full primitive
pullback identity, actual differential and actual exterior derivative
produce the radial equation; no field or integral-curve equation is
assumed. These conditional local calculations do not construct the
half-infinite cylinder attachment or prove its coverage.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry.PrescribedCylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual outward cylinder one-form, including its zero radial coefficient. -/
def cylinderPrimitive (α : E → E [⋀^Fin 1]→L[ℝ] ℝ) (p : ℝ × E) :
    (ℝ × E) [⋀^Fin 1]→L[ℝ] ℝ :=
  Real.exp p.1 • (α p.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ ℝ E)

/-- Exterior differentiation of the prescribed coefficients gives contraction
by the constant outward radial vector. Only local spatial differentiability is needed. -/
theorem extDeriv_cylinderPrimitive_radial
    (α : E → E [⋀^Fin 1]→L[ℝ] ℝ) (p v : ℝ × E)
    (hα : DifferentiableAt ℝ α p.2) :
    extDeriv (cylinderPrimitive α) p ![(1, 0), v] =
      cylinderPrimitive α p (fun _ => v) := by
  let β : ℝ × E → (ℝ × E) [⋀^Fin 1]→L[ℝ] ℝ := fun q =>
    (α q.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ ℝ E)
  let L := ContinuousAlternatingMap.compContinuousLinearMapCLM
    (F := ℝ) (ι := Fin 1) (ContinuousLinearMap.snd ℝ ℝ E)
  have hβ : HasFDerivAt β
      (L.comp ((fderiv ℝ α p.2).comp (ContinuousLinearMap.snd ℝ ℝ E))) p :=
    L.hasFDerivAt.comp p (hα.hasFDerivAt.comp p hasFDerivAt_snd)
  have hβrad : fderiv ℝ β p (1, 0) = 0 := by
    rw [hβ.fderiv]
    simp
  have hβzero : β p (fun _ => (1, 0)) = 0 := by
    change (α p.2) (fun _ => 0) = 0
    exact (α p.2).map_coord_zero (i := 0) rfl
  have hβext : extDeriv β p ![(1, 0), v] = 0 := by
    rw [LiouvilleFlowPrimitive.extDeriv_one_apply, hβrad, hβ.fderiv]
    simp [L, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
    exact ((fderiv ℝ α p.2) v.2).map_coord_zero (i := 0) rfl
  have he : HasFDerivAt (fun q : ℝ × E => Real.exp q.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (Real.exp p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ E)) p :=
    (Real.hasDerivAt_exp p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have herad : fderiv ℝ (fun q : ℝ × E => Real.exp q.1) p (1, 0) = Real.exp p.1 := by
    rw [he.fderiv]
    simp
  change extDeriv (fun q => Real.exp q.1 • β q) p ![(1, 0), v] =
    (Real.exp p.1 • β p) (fun _ => v)
  rw [FormScalarDerivative.extDeriv_variable_smul_one_apply
    (fun q : ℝ × E => Real.exp q.1) β p (1, 0) v he.differentiableAt hβ.differentiableAt,
    hβext, herad, hβzero]
  simp [β]

open SmoothManifold

/-- A smooth cylinder parametrization satisfying the full primitive identity
has the radial contraction equation in the given ambient, by exterior naturality.
Surjectivity of the actual differential lets the equation test every ambient tangent. -/
theorem radial_liouvilleEquation {d : ℕ} (X : SmoothManifold d)
    (lambda : X.Form 1) (hlambda : X.IsSmoothForm lambda)
    (F : ℝ × E → X.Point) {U : Set (ℝ × E)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞ F U)
    (α : E → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hprimitive : ∀ q ∈ U, (lambda (F q)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F q) = cylinderPrimitive α q)
    {p : ℝ × E} (hp : p ∈ U) (hα : DifferentiableAt ℝ α p.2)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p)) :
    X.LiouvilleEquation lambda (F p)
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0)) := by
  intro w
  obtain ⟨v, rfl⟩ := hsurj w
  have heq : (fun q => (lambda (F q)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F q)) =ᶠ[𝓝 p]
      cylinderPrimitive α := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hprimitive q hq
  have hnat := congrArg (fun η => η ![(1, 0), v])
    (X.exteriorDerivative_pullback_from_normedSpace_on F hU hF lambda hlambda hp)
  rw [heq.extDeriv_eq, extDeriv_cylinderPrimitive_radial α p v hα] at hnat
  have hpull := congrArg (fun η => η (fun _ => v)) (hprimitive p hp)
  have hpair : (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p) ∘ ![(1, 0), v] =
      ![mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0),
        mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p v] := by
    funext i
    fin_cases i <;> rfl
  change _ = (X.exteriorDerivative lambda (F p))
    ((mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p) ∘ ![(1, 0), v]) at hnat
  rw [hpair] at hnat
  exact hnat.symm.trans hpull.symm

/-- Nondegeneracy identifies the actual primitive's canonical Liouville field
with the derivative of the outward radial coordinate curve. -/
theorem liouvilleVector_eq_radial {d : ℕ} (X : SmoothManifold d)
    (lambda : X.Form 1) (hlambda : X.IsSmoothForm lambda)
    (F : ℝ × E → X.Point) {U : Set (ℝ × E)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞ F U)
    (α : E → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hprimitive : ∀ q ∈ U, (lambda (F q)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F q) = cylinderPrimitive α q)
    {p : ℝ × E} (hp : p ∈ U) (hα : DifferentiableAt ℝ α p.2)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p))
    (hnd : X.Nondegenerate (X.exteriorDerivative lambda) (F p)) :
    X.liouvilleVector lambda (F p) =
      mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0) :=
  X.liouvilleVector_eq lambda (F p) hnd
    (radial_liouvilleEquation X lambda hlambda F hU hF α hprimitive hp hα hsurj)

/-- On a genuinely half-infinite signed cylinder chart, the actual radial
coordinate curves solve the canonical ambient Liouville ODE. The spatial
form is required smooth only on the chart's open spatial domain. -/
theorem isMIntegralCurveOn_radial {d : ℕ} (X : SmoothManifold d)
    (lambda : X.Form 1) (hlambda : X.IsSmoothForm lambda)
    (F : ℝ × E → X.Point) {a : ℝ} {V : Set E} (hV : IsOpen V)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞ F (Ioi a ×ˢ V))
    (α : E → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : ContDiffOn ℝ ∞ α V)
    (hprimitive : ∀ p ∈ Ioi a ×ˢ V, (lambda (F p)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p) = cylinderPrimitive α p)
    (hsurj : ∀ p ∈ Ioi a ×ˢ V,
      Function.Surjective (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p))
    (hnd : ∀ p ∈ Ioi a ×ˢ V, X.Nondegenerate (X.exteriorDerivative lambda) (F p))
    {y : E} (hy : y ∈ V) :
    IsMIntegralCurveOn (fun r => F (r, y)) (X.liouvilleVector lambda) (Ioi a) := by
  intro r hr
  have hp : (r, y) ∈ Ioi a ×ˢ V := ⟨hr, hy⟩
  have hU : IsOpen (Ioi a ×ˢ V) := isOpen_Ioi.prod hV
  have hFd := ((hF (r, y) hp).contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  have hcurve : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × E)
      (fun s : ℝ => (s, y)) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (1, (0 : E))) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr
      (((hasDerivAt_id r).prodMk (hasDerivAt_const r y)).hasFDerivAt)
  have hderiv := hFd.hasMFDerivAt.comp r hcurve
  have hαd : DifferentiableAt ℝ α y :=
    ((hα y hy).contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
  apply (hderiv.congr_mfderiv ?_).hasMFDerivWithinAt
  rw [liouvilleVector_eq_radial X lambda hlambda F hU hF α hprimitive hp
    hαd (hsurj (r, y) hp) (hnd (r, y) hp)]
  apply ContinuousLinearMap.ext
  intro s
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul]

end FsFltz.Geometry.PrescribedCylinder
