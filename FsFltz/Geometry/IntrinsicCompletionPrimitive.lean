import FsFltz.Geometry.IntrinsicCompletionCylinder
import FsFltz.Geometry.IntrinsicGluedFormRestriction
import FsFltz.Geometry.IntrinsicExtensionSymplectic

/-!
# One symplectic primitive on the actual intrinsic completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158, and `sec:lean`,
lines 783–814. The finite primitive and the full exponential cylinder
primitive are glued through actual quotient patch differentials. Compatibility
is proved from the same native Liouville collar; no global primitive is input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

local instance primitiveFullBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance primitiveFullBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ
local instance primitiveFiniteBandCharts : ChartedSpace (Model (k + 1))
    (IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M)) :=
  IntrinsicCollarGluing.bandChartedSpace δ
local instance primitiveFiniteBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (IntrinsicCollarGluing.Band δ (IntrinsicBoundary.Point k M)) :=
  IntrinsicCollarGluing.band_isManifold δ

/-- The actual finite-window primitive and whole-cylinder primitive give
the same ambient covector at every point of their actual overlap. -/
theorem pushedPrimitive_overlap
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    (u : IntrinsicCollarGluing.Extension
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hup : finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) u =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) :
    SmoothManifold.pushOneForm
      (IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero)
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
      (bijective_mfderiv_finiteIn hδ C hemb hC hboundary hinv hzero)
      (IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α) u =
    SmoothManifold.pushOneForm
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M))
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
      (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero)
      (cylinderPrimitive δ α) p := by
  let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let Q := IntrinsicCollarGluing.bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let c := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let i := finiteIn c
  let j := cylinder c
  let f := IntrinsicCollarGluing.cylinder c
  let b := IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α
  let η := cylinderPrimitive δ α
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  obtain ⟨q, rfl, rfl⟩ := (finiteIn_eq_cylinder_iff hδ C hemb u p).mp hup
  let A := mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i (f q)
  let B := mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) f q
  let J := mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j (finiteBandIn q)
  let D := mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) finiteBandIn q
  have hd₁ := mfderiv_comp q
    ((contMDiff_finiteIn hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    ((IntrinsicCollarGluing.contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp q
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    ((contMDiff_finiteBandIn δ).mdifferentiableAt (by simp))
  have heq : A.comp B = J.comp D := hd₁.symm.trans hd₂
  have hA := SmoothManifold.pullback_pushOneForm N X i
    (bijective_mfderiv_finiteIn hδ C hemb hC hboundary hinv hzero) b (f q)
  have hJ := SmoothManifold.pullback_pushOneForm P X j
    (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero) η (finiteBandIn q)
  have hf := congrFun (IntrinsicCollarGluing.pullback_gluedPrimitive_cylinder
    hδ C hemb hC hboundary hinv hzero α hα Z hZ hode) q
  have hg := congrFun (pullback_cylinderPrimitive_finiteBandIn δ α) q
  have hAB : Function.Surjective (A.comp B) := by
    intro v
    obtain ⟨w, hw⟩ := (bijective_mfderiv_finiteIn hδ C hemb hC hboundary hinv hzero (f q)).2 v
    obtain ⟨z, hz⟩ :=
      (IntrinsicCollarGluing.bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero q).2 w
    exact ⟨z, by change A (B z) = v; rw [hz]; exact hw⟩
  apply SmoothManifold.form_eq_of_comp_eq (d := k + 1) (r := 1)
    (E := Model (k + 1)) _ _ (A.comp B) hAB
  calc
    _ = (b (f q)).compContinuousLinearMap B := by
      ext vs
      exact congrArg (fun β => β (fun n => B (vs n))) hA
    _ = IntrinsicCollarGluing.cylinderPrimitive δ α q := hf
    _ = (η (finiteBandIn q)).compContinuousLinearMap D := hg.symm
    _ = _ := by
      rw [heq]
      ext vs
      exact congrArg (fun β => β (fun n => D (vs n))) hJ.symm

/-- One globally smooth primitive on the actual half-infinite quotient,
with exact finite-patch and full-cylinder pullbacks. All compatibility comes
from the native primitive and the same collar's Liouville equation and ODE. -/
theorem exists_smooth_primitive
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ)) :
    let X := completionManifold hδ C hemb hC hboundary hinv hzero
    let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
    let c := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
    ∃ lam : X.Form 1, X.IsSmoothForm lam ∧
      N.pullback X (finiteIn c) lam =
        IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α ∧
      P.pullback X (cylinder c) lam = cylinderPrimitive δ α := by
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let c := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  apply SmoothManifold.exists_smoothForm_of_two_open_patches X N P (finiteIn c) (cylinder c)
    (contMDiff_finiteIn hδ C hemb hC hboundary hinv hzero)
    (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero)
    (finiteIn_injective c) (cylinder_injective c hemb.injective)
    (bijective_mfderiv_finiteIn hδ C hemb hC hboundary hinv hzero)
    (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero)
    (fun u => by
      obtain ⟨g, hg, _, heq⟩ := finiteIn_inverse_germ hδ C hemb hC hboundary hinv hzero u
      exact ⟨g, hg, heq⟩)
    (fun p => by
      obtain ⟨g, hg, _, heq⟩ := cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero p
      exact ⟨g, hg, heq⟩)
    (completion_open_cover C)
    (IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α)
    (cylinderPrimitive δ α)
    (IntrinsicCollarGluing.isSmoothForm_gluedPrimitive hδ C hemb hC hboundary hinv hzero
      α hα Z hZ hode)
    (isSmoothForm_cylinderPrimitive δ α hα)
    (pushedPrimitive_overlap hδ C hemb hC hboundary hinv hzero α hα Z hZ hode)

/-- Finite-patch primitive preservation gives full native primitive preservation,
including every tangent based at the original boundary seam. -/
theorem pullback_primitive_original
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    (lam : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hfinite : (IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (finiteIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) lam =
        IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    (fun x => (lam (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x)) = α := by
  let c := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let i := finiteIn c
  let o := IntrinsicCollarGluing.original c
  let b := IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  have hnative := IntrinsicCollarGluing.pullback_gluedPrimitive_original
    hδ C hemb hC hboundary hinv hzero α hα Z hZ hode
  funext x
  have hd := mfderiv_comp x
    ((contMDiff_finiteIn hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    ((IntrinsicCollarGluing.contMDiff_original hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
  have hfp := congrFun hfinite (o x)
  change (lam (i (o x))).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i (o x)) = b (o x) at hfp
  calc
    _ = ((lam (i (o x))).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i (o x))).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) o x) := by
      ext vs
      change lam ((i ∘ o) x) (fun n =>
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (i ∘ o) x (vs n)) = _
      rw [hd]
      rfl
    _ = (b (o x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) o x) := by rw [hfp]
    _ = α x := congrFun hnative x

/-- The actual completion differential is nondegenerate everywhere. Native
points use exterior naturality; every new cylinder point is reached from
its native seam by a smooth time translation and nonzero constant scaling. -/
theorem nondegenerate_primitive_of_patch_pullbacks
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (lam : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hlam : (completionManifold hδ C hemb hC hboundary hinv hzero).IsSmoothForm lam)
    (hnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      (fun x => (lam (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x)) = α)
    (hcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) lam =
        cylinderPrimitive δ α) :
    ∀ x, (completionManifold hδ C hemb hC hboundary hinv hzero).Nondegenerate
      ((completionManifold hδ C hemb hC hboundary hinv hzero).exteriorDerivative lam) x := by
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let c := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let j := cylinder c
  let η := cylinderPrimitive δ α
  let := completionChartedSpace hδ C hemb hboundary hzero
  have hnativeND (x : M) : X.Nondegenerate (X.exteriorDerivative lam) (original c x) :=
    IntrinsicLiouville.nondegenerate_exteriorDerivative_of_native_pullback X (original c)
      (contMDiff_original hδ C hemb hC hboundary hinv hzero) lam hlam α hnative x
      (bijective_mfderiv_original hδ C hemb hC hboundary hinv hzero x) (hnd x)
  intro x
  rcases jointly_surjective c x with ⟨u, rfl⟩ | ⟨p, rfl⟩
  · exact hnativeND u
  · by_cases hp : 0 ≤ p.val.1
    · have he : original c (C p.val) = cylinder c p :=
        original_collar_eq_cylinder c (halfOfNonneg p hp)
      rw [← he]
      exact hnativeND (C p.val)
    · have hpneg : p.val.1 ≤ 0 := (lt_of_not_ge hp).le
      let q : Band δ (IntrinsicBoundary.Point k M) :=
        ⟨(0, p.val.2), hδ, mem_univ _⟩
      have hseam : j q = original c p.val.2.val := by
        have he := original_collar_eq_cylinder c
          (show Half δ (IntrinsicBoundary.Point k M) from
            ⟨(0, p.val.2), ⟨le_rfl, hδ⟩, mem_univ _⟩)
        change original c (C (0, p.val.2)) = j q at he
        rw [hzero] at he
        exact he.symm
      have hnq : X.Nondegenerate (X.exteriorDerivative lam) (j q) := by
        rw [hseam]
        exact hnativeND p.val.2.val
      have hηq : P.Nondegenerate (P.exteriorDerivative η) q := by
        have h := SmoothManifold.nondegenerate_exteriorDerivative_pullback P X j
          (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero) lam hlam q
          (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero q) hnq
        rwa [hcylinder] at h
      have hη := isSmoothForm_cylinderPrimitive δ α hα
      let s : P.Point → P.Point := inwardShift p.val.1 hpneg
      have hs : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ s :=
        contMDiff_inwardShift δ p.val.1 hpneg
      have hsq : s q = p := by
        apply Subtype.ext
        change (0 + p.val.1, p.val.2) = p.val
        simp
      have hscaled : P.Nondegenerate
          (P.exteriorDerivative (fun u => Real.exp (-p.val.1) • η u)) q :=
        SmoothManifold.nondegenerate_exteriorDerivative_const_smul P η hη
          (Real.exp (-p.val.1)) (Real.exp_ne_zero _) q hηq
      have hηp : P.Nondegenerate (P.exteriorDerivative η) p := by
        have h := SmoothManifold.nondegenerate_exteriorDerivative_of_pullback P P s hs
          η hη (fun u => Real.exp (-p.val.1) • η u)
          (pullback_cylinderPrimitive_inwardShift δ p.val.1 hpneg α) q
          (bijective_mfderiv_inwardShift p.val.1 hpneg q) hscaled
        rwa [hsq] at h
      exact SmoothManifold.nondegenerate_exteriorDerivative_of_pullback P X j
        (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero) lam hlam η hcylinder p
        (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero p) hηp

/-- The single constructed primitive has globally symplectic differential,
full native restriction and the exponential law on the entire infinite end.
The proof takes only local native Liouville collar data, never a desired
global primitive, symplectic form, complete field, or completion. -/
theorem exists_smooth_symplectic_primitive
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ)) :
    let X := completionManifold hδ C hemb hC hboundary hinv hzero
    let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
    let c := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ∃ lam : X.Form 1, X.IsSmoothForm lam ∧
      N.pullback X (finiteIn c) lam =
        IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α ∧
      (fun x => (lam (original c x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x)) = α ∧
      P.pullback X (cylinder c) lam = cylinderPrimitive δ α ∧
      ∀ x, X.Nondegenerate (X.exteriorDerivative lam) x := by
  obtain ⟨lam, hlam, hfinite, hcylinder⟩ :=
    exists_smooth_primitive hδ C hemb hC hboundary hinv hzero α hα Z hZ hode
  have hnative := pullback_primitive_original hδ C hemb hC hboundary hinv hzero
    α hα Z hZ hode lam hfinite
  exact ⟨lam, hlam, hfinite, hnative, hcylinder,
    nondegenerate_primitive_of_patch_pullbacks hδ C hemb hC hboundary hinv hzero
      α hα hnd lam hlam hnative hcylinder⟩

end FsFltz.Geometry.IntrinsicCompletionGluing
