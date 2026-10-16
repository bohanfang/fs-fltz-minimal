import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.Complement

/-!
# Product coordinates preserving an actual submersion

Source: `geometric-part-fsf-proof.tex`, `lem:trapping`, lines 1672–1696.
An actual derivative with a specified normal right inverse constructs local
product coordinates by the inverse function theorem. The second coordinate
is the original defining map, and the derivative of the inverse in that
coordinate is the specified normal lift. No tubular chart is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz.Geometry

open Set Filter Function
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Split the domain into the defining-map kernel and the supplied normal
lift. The projection is along this lift, rather than an independent choice. -/
def submersionProductEquiv (A : E →L[ℝ] F) (L : F →L[ℝ] E)
    (hL : RightInverse L A) : E ≃L[ℝ] A.ker × F :=
  (ContinuousLinearEquiv.equivOfRightInverse A L hL).trans
    (ContinuousLinearEquiv.prodComm ℝ F A.ker)

@[simp] theorem submersionProductEquiv_apply (A : E →L[ℝ] F) (L : F →L[ℝ] E)
    (hL : RightInverse L A) (x : E) :
    submersionProductEquiv A L hL x = (A.projKerOfRightInverse L hL x, A x) := rfl

@[simp] theorem submersionProductEquiv_symm_apply (A : E →L[ℝ] F)
    (L : F →L[ℝ] E) (hL : RightInverse L A) (p : A.ker × F) :
    (submersionProductEquiv A L hL).symm p = L p.2 + p.1 := rfl

/-- The local inverse preserves the literal defining map and has the
chosen normal derivative, including in zero normal dimension. -/
theorem exists_submersion_product_coordinates [CompleteSpace E]
    (δ : E → F) (a : E) (A : E →L[ℝ] F) (L : F →L[ℝ] E)
    (hL : RightInverse L A) (hδ : ContDiffAt ℝ ∞ δ a)
    (hA : HasFDerivAt δ A a) (hzero : δ a = 0) :
    ∃ e : OpenPartialHomeomorph E (A.ker × F),
      a ∈ e.source ∧ (0 : A.ker × F) ∈ e.target ∧ e a = 0 ∧
      (∀ y, e y = (A.projKerOfRightInverse L hL (y - a), δ y)) ∧
      ContDiffAt ℝ ∞ e.symm 0 ∧
      HasFDerivAt e.symm (submersionProductEquiv A L hL).symm.toContinuousLinearMap 0 ∧
      ((fderiv ℝ e.symm 0).comp (ContinuousLinearMap.inr ℝ A.ker F) = L) ∧
      (∀ p ∈ e.target, δ (e.symm p) = p.2) := by
  let P := A.projKerOfRightInverse L hL
  let κ : E → A.ker × F := fun y => (P (y - a), δ y)
  have hκ : ContDiffAt ℝ ∞ κ a :=
    ((P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt).prodMk hδ
  have hκA : HasFDerivAt κ (submersionProductEquiv A L hL).toContinuousLinearMap a := by
    exact ((P.hasFDerivAt).comp a ((hasFDerivAt_id a).sub_const a)).prodMk hA
  have hκzero : κ a = 0 := by simp [κ, hzero]
  let e := hκ.toOpenPartialHomeomorph κ (f' := submersionProductEquiv A L hL) hκA (by simp)
  have ha : a ∈ e.source := hκ.mem_toOpenPartialHomeomorph_source hκA (by simp)
  have ht : (0 : A.ker × F) ∈ e.target := by
    simpa only [hκzero] using hκ.image_mem_toOpenPartialHomeomorph_target hκA (by simp)
  have hs : ContDiffAt ℝ ∞ e.symm 0 := by
    simpa only [hκzero, e, ContDiffAt.toOpenPartialHomeomorph,
      ContDiffAt.localInverse, HasStrictFDerivAt.localInverse] using
      hκ.to_localInverse (f' := submersionProductEquiv A L hL) hκA (by simp)
  have hd : HasFDerivAt e.symm
      (submersionProductEquiv A L hL).symm.toContinuousLinearMap 0 := by
    simpa only [hκzero, e, ContDiffAt.toOpenPartialHomeomorph,
      HasStrictFDerivAt.localInverse] using
      (hκ.hasStrictFDerivAt' hκA (by simp)).to_localInverse
        (f' := submersionProductEquiv A L hL) |>.hasFDerivAt
  refine ⟨e, ha, ht, hκzero, fun _ => rfl, hs, hd, ?_, ?_⟩
  · rw [hd.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    simp
  · intro p hp
    exact congrArg Prod.snd (e.right_inv hp)

end FsFltz.Geometry
