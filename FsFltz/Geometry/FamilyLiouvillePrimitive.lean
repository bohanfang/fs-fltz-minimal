import FsFltz.Geometry.FamilyLiouvilleLocalFlow
import FsFltz.Geometry.LiouvilleFlowPrimitive

/-!
# Primitive scaling on the same family boundary flow

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158,
`def:chain`, lines 163–169, `lem:shrinking`, lines 624–628, and
`sec:lean`, lines 805–821. The supplied flow is the constructed auxiliary
parameter-preserving action. Its actual local Liouville ODE and contraction
equation on the boundary trajectories imply the exponential primitive law
for that same boundary-flow map, including the radial differential.

The Liouville equations are required only along the local trajectory tube
and for parameters in `[0,1]`. Neither a new flow nor a primitive-scaling
certificate is supplied. This law does not construct a completed family or
assert completeness of the original Liouville fields.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace CompactDomain

set_option backward.isDefEq.respectTransparency false in
/-- The same jointly smooth family boundary flow pulls the actual interval
primitive back to its exponential boundary primitive. The full differential
includes every spatial tangent and radial speed. Only the native ODE and
canonical contraction on the local boundary trajectories are assumed. -/
theorem localBoundaryFamilyFlow_primitive {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (F : Flow ℝ (ℝ × D.extension.Point))
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × (ℝ × D.extension.Point) => F p.1 p.2))
    {δ : ℝ} (hδ : 0 < δ)
    (hcontract : ∀ (a : Parameter) (x : D.boundary.Point), ∀ r ∈ Ioo (-δ) δ,
      D.extension.LiouvilleEquation ((L a).primitive)
        (F r (a.val, D.boundaryInclusion.map x)).2
        (D.extension.liouvilleVector ((L a).primitive)
          (F r (a.val, D.boundaryInclusion.map x)).2))
    (hode : ∀ (a : Parameter) (x : D.boundary.Point), ∀ r ∈ Ioo (-δ) δ,
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun s => (F s (a.val, D.boundaryInclusion.map x)).2) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (D.extension.liouvilleVector ((L a).primitive)
            (F r (a.val, D.boundaryInclusion.map x)).2)))
    (a : Parameter) (x : D.boundary.Point) {r : ℝ} (hr : r ∈ Ioo (-δ) δ)
    (v : Model (d - 1)) (s : ℝ) :
    evalOne ((L a).primitive) (F r (a.val, D.boundaryInclusion.map x)).2
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        (fun p : D.boundary.Point × ℝ =>
          (F p.2 (a.val, D.boundaryInclusion.map p.1)).2) (x, r) (v, s)) =
      Real.exp r * evalOne (D.boundaryForm ((L a).primitive)) x v := by
  let B := D.boundary
  let M := D.extension
  let j := D.boundaryInclusion.map
  let c : B.Point × ℝ → M.Point := fun p => (F p.2 (a.val, j p.1)).2
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
      𝓘(ℝ, Model d) ∞ (fun p : ℝ × (ℝ × M.Point) => (F p.1 p.2).2) :=
    contMDiff_snd.comp hF
  have hc : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ c :=
    hs.comp (contMDiff_snd.prodMk
      (contMDiff_const.prodMk (j.contMDiff.comp contMDiff_fst)))
  have hct : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model d) ∞ (fun p : ℝ × B.Point => (F p.1 (a.val, j p.2)).2) :=
    hs.comp (contMDiff_fst.prodMk
      (contMDiff_const.prodMk (j.contMDiff.comp contMDiff_snd)))
  have hp := LiouvilleFlowPrimitive.pullback_slice_eq_exp_smul_of_local_contraction M B
    (L a).primitive (L a).smooth_primitive (M.liouvilleVector (L a).primitive)
    (fun p : ℝ × B.Point => (F p.1 (a.val, j p.2)).2) hct
    isOpen_Ioo isPreconnected_Ioo isOpen_univ
    (fun p hp => hcontract a p.2 p.1 hp.1)
    (fun y _ t ht => hode a y t ht) hr
    (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨neg_lt_zero.mpr hδ, hδ⟩) (mem_univ x)
  have hinit : (fun y : B.Point => (F 0 (a.val, j y)).2) = j :=
    funext (fun y => congrArg Prod.snd (F.map_zero_apply _))
  rw [hinit, sub_zero] at hp
  have hval := congrArg (fun alpha => alpha (fun _ : Fin 1 => v)) hp
  have hi : HasMFDerivAt 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (fun y : B.Point => (y, r)) x
      ((ContinuousLinearMap.id ℝ (Model (d - 1))).prod 0) :=
    (hasMFDerivAt_id x).prodMk (hasMFDerivAt_const r x)
  have hspace := mfderiv_comp_apply (f := fun y : B.Point => (y, r)) (g := c) x
    (hc.mdifferentiableAt (by simp)) hi.mdifferentiableAt v
  rw [hi.mfderiv] at hspace
  change mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
      (fun y => (F r (a.val, j y)).2) x v =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (v, 0)
      at hspace
  have ht : HasMFDerivAt 𝓘(ℝ, ℝ)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (fun t : ℝ => (x, t)) r
      ((0 : ℝ →L[ℝ] Model (d - 1)).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const x r).prodMk (hasMFDerivAt_id r)
  have htime := mfderiv_comp_apply (f := fun t : ℝ => (x, t)) (g := c) r
    (hc.mdifferentiableAt (by simp)) ht.mdifferentiableAt (1 : ℝ)
  rw [ht.mfderiv] at htime
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun t => (F t (a.val, j x)).2) r (1 : ℝ) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (0, 1)
      at htime
  rw [(hode a x r hr).mfderiv] at htime
  change (1 : ℝ) • M.liouvilleVector ((L a).primitive) (F r (a.val, j x)).2 =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (0, 1)
      at htime
  rw [one_smul] at htime
  have hsplit : (v, s) = (v, (0 : ℝ)) + s • (0, (1 : ℝ)) := by simp
  change evalOne ((L a).primitive) (F r (a.val, j x)).2
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (v, s)) = _
  rw [hsplit, map_add, map_smul, ← hspace, ← htime, evalOne_add, evalOne_smul,
    M.evalOne_eq_zero_of_liouvilleEquation _ _ _ (hcontract a x r hr),
    mul_zero, add_zero]
  exact hval

end CompactDomain
end FsFltz.Geometry
