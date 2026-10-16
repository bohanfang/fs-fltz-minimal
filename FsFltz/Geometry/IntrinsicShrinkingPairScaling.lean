import FsFltz.Geometry.FormScalarDerivative
import FsFltz.Geometry.SmoothForms
import FsFltz.Geometry.Deformation

/-!
# Positive scaling of a ribbon and its specified completion

Source: `geometric-part-fsf-proof.tex`, `lem:shrinking`, lines 470–488;
`subsec:junction`, lines 1876–1892; and `geoemtric-part-fsf.tex`,
`lem:shrinking`, lines 605–629. Constant scaling retains the actual field,
complete flow, compact inclusion and end maps. These are constructions,
not supplied completion-family certificates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

/-- The actual exterior derivative is linear under a constant real scale. -/
theorem exteriorDerivative_const_smul_one {d : ℕ} (M : SmoothManifold d)
    (α : M.Form 1) (hα : M.IsSmoothForm α) (c : ℝ) :
    M.exteriorDerivative (c • α) = c • M.exteriorDerivative α := by
  funext x
  ext vs
  have h := M.evalTwo_exteriorDerivative_smul (fun _ => c) α contMDiff_const hα
    x (vs 0) (vs 1)
  have hv : vs = ![vs 0, vs 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  change (M.exteriorDerivative (fun y => c • α y) x) ![vs 0, vs 1] =
    c * (M.exteriorDerivative α x) ![vs 0, vs 1]
  simpa only [evalTwo, scalarDerivative, mfderiv_const, zero_apply,
    zero_mul, add_zero, sub_zero, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] using h

end SmoothManifold

namespace LiouvilleStructure

/-- Scale a compact ribbon primitive by a positive constant, retaining its field. -/
def positiveScale {d : ℕ} {D : CompactDomain d} (L : LiouvilleStructure D)
    (c : ℝ) (hc : 0 < c) : LiouvilleStructure D where
  primitive := c • L.primitive
  smooth_primitive := L.smooth_primitive.smul c
  symplectic := by
    apply (D.extension.isSymplecticOn_exteriorDerivative_iff _
      (L.smooth_primitive.smul c) _).mpr
    intro x hx v hv
    apply L.symplectic.2.2 x hx v
    intro w
    have h := hv w
    rw [D.extension.exteriorDerivative_const_smul_one L.primitive L.smooth_primitive c] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hc)
  field := L.field
  smooth_field := L.smooth_field
  contraction := by
    intro x hx v
    rw [D.extension.exteriorDerivative_const_smul_one L.primitive L.smooth_primitive c]
    exact congrArg (fun z : ℝ => c * z) (L.contraction x hx v)
  outward := L.outward

@[simp] theorem positiveScale_primitive {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (c : ℝ) (hc : 0 < c) :
    (L.positiveScale c hc).primitive = c • L.primitive := rfl

@[simp] theorem positiveScale_field {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (c : ℝ) (hc : 0 < c) :
    (L.positiveScale c hc).field = L.field := rfl

@[simp] theorem positiveScale_one {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (hc : 0 < (1 : ℝ)) : L.positiveScale 1 hc = L := by
  cases L
  simp only [positiveScale, one_smul]

end LiouvilleStructure

namespace CompleteLiouvilleManifold

/-- Scale the primitive on a specified completed ribbon, retaining the entire flow. -/
def positiveScale {d : ℕ} (X : CompleteLiouvilleManifold d) (c : ℝ) (hc : 0 < c) :
    CompleteLiouvilleManifold d where
  manifold := X.manifold
  primitive := c • X.primitive
  smooth_primitive := X.smooth_primitive.smul c
  symplectic := by
    apply (X.manifold.isSymplecticOn_exteriorDerivative_iff _
      (X.smooth_primitive.smul c) _).mpr
    intro x hx v hv
    apply X.symplectic.2.2 x hx v
    intro w
    have h := hv w
    rw [X.manifold.exteriorDerivative_const_smul_one X.primitive X.smooth_primitive c] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hc)
  field := X.field
  smooth_field := X.smooth_field
  contraction := by
    intro x v
    rw [X.manifold.exteriorDerivative_const_smul_one X.primitive X.smooth_primitive c]
    exact congrArg (fun z : ℝ => c * z) (X.contraction x v)
  completeFlow := X.completeFlow

@[simp] theorem positiveScale_one {d : ℕ} (X : CompleteLiouvilleManifold d)
    (hc : 0 < (1 : ℝ)) : X.positiveScale 1 hc = X := by
  cases X
  simp only [positiveScale, one_smul]

end CompleteLiouvilleManifold

namespace Completion

/-- The same completed ribbon, compact inclusion and end coordinate realize
the positive constant scaling of a compact ribbon. -/
def positiveScale {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (c : ℝ) (hc : 0 < c) :
    Completion (⟨D.domain, D.liouville.positiveScale c hc⟩ : LiouvilleDomain d) where
  ambient := C.ambient.positiveScale c hc
  inclusion := C.inclusion
  primitive_on_domain := by
    intro x hx
    ext vs
    exact congrArg (fun z : ℝ => c * z)
      (congrArg (fun η => η vs) (C.primitive_on_domain x hx))
  field_on_domain := C.field_on_domain
  endMap := C.endMap
  smooth_endMap := C.smooth_endMap
  end_flow := C.end_flow
  end_embedding := C.end_embedding
  end_immersion := C.end_immersion
  end_primitive := by
    intro x r v s
    have h := congrArg (fun z : ℝ => c * z) (C.end_primitive x r v s)
    change c * evalOne C.ambient.primitive (C.endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endMap (x, r) (v, s)) =
      Real.exp r * (c * evalOne (D.domain.boundaryForm D.liouville.primitive) x v)
    exact h.trans (by ring)
  covering := C.covering
  overlap := C.overlap

/-- Scaling retains the entire all-forward-time core on the same compact carrier. -/
@[simp] theorem positiveScale_core {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (c : ℝ) (hc : 0 < c) : (C.positiveScale c hc).core = C.core := rfl

end Completion

namespace SmoothManifold

/-- The shrinking constants have a smooth extension for all real parameters,
also on the noncompact completed ribbon. -/
theorem isSmoothIntervalFormFamily_expScale {d : ℕ} (M : SmoothManifold d)
    (α : M.Form 1) (hα : M.IsSmoothForm α) (T : ℝ) :
    M.IsSmoothIntervalFormFamily (fun t => Real.exp (-(T * t.val)) • α) := by
  refine ⟨fun t => Real.exp (-(T * t)) • α, ?_, fun _ => rfl⟩
  intro a
  refine ⟨univ ×ˢ (chartAt (Model d) a).target,
    isOpen_univ.prod (chartAt (Model d) a).open_target,
    prod_mono (subset_univ _) (subset_refl _), ?_⟩
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Model d => Real.exp (-(T * p.1))) :=
    Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg)
  have hc : ContDiffOn ℝ ∞ (fun p : ℝ × Model d => M.formInChart a α p.2)
      (univ ×ˢ (chartAt (Model d) a).target) :=
    (hα a).comp contDiffOn_snd (fun _ hp => hp.2)
  apply (hs.contDiffOn.smul hc).congr
  intro p _
  rw [M.formInChart_smul]
  rfl

end SmoothManifold
end FsFltz.Geometry
