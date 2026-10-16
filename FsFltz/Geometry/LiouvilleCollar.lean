import FsFltz.Geometry.LiouvilleCollarSide
import FsFltz.Geometry.LiouvilleFlowPrimitive

/-!
# A constructed Liouville collar with its actual primitive

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–158, and `sec:lean`,
lines 783–814. The same constructed boundary flow has a uniform injective
smooth collar, its exact domain-side equation, and the exponential primitive
formula. The latter follows from the intrinsic flow pullback theorem; the
time component vanishes by alternation and the Liouville equation.
No completion, collar, or primitive-scaling identity is supplied as input.
Constructing the completed manifold and its complete Liouville flow remains
a separate foundation, and the main geometric target remains unproved.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace LiouvilleDomain

set_option backward.isDefEq.respectTransparency false in
/-- The full boundary-flow differential, including its time component, pulls
the actual primitive back to the exponential boundary primitive. -/
theorem localBoundaryFlow_primitive {d : ℕ} (D : LiouvilleDomain d)
    (F : Flow ℝ D.neighborhoodDomain.extension.Point)
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.neighborhoodDomain.extension.Point => F p.1 p.2))
    {δ : ℝ} (hδ : 0 < δ)
    (hode : ∀ x : D.neighborhoodDomain.boundary.Point, ∀ t ∈ Ioo (-δ) δ,
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun s => F s (D.neighborhoodDomain.boundaryInclusion.map x)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (D.neighborhoodStructure.field
          (F t (D.neighborhoodDomain.boundaryInclusion.map x)))))
    (x : D.neighborhoodDomain.boundary.Point) {r : ℝ} (hr : r ∈ Ioo (-δ) δ)
    (v : Model (d - 1)) (s : ℝ) :
    evalOne D.neighborhoodStructure.primitive
      (F r (D.neighborhoodDomain.boundaryInclusion.map x))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
          F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (x, r) (v, s)) =
      Real.exp r * evalOne
        (D.neighborhoodDomain.boundaryForm D.neighborhoodStructure.primitive) x v := by
  let B := D.neighborhoodDomain.boundary
  let M := D.neighborhoodDomain.extension
  let j := D.neighborhoodDomain.boundaryInclusion.map
  let c : B.Point × ℝ → M.Point := fun p => F p.2 (j p.1)
  have hc : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ c :=
    hF.comp (contMDiff_snd.prodMk (j.contMDiff.comp contMDiff_fst))
  have hct : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model d) ∞ (fun p : ℝ × B.Point => F p.1 (j p.2)) :=
    hF.comp (contMDiff_fst.prodMk (j.contMDiff.comp contMDiff_snd))
  have hp := LiouvilleFlowPrimitive.pullback_slice_eq_exp_smul M B
    D.neighborhoodStructure.primitive D.neighborhoodStructure.smooth_primitive
    D.neighborhoodStructure.field D.neighborhood_contraction
    (fun p : ℝ × B.Point => F p.1 (j p.2)) hct isOpen_Ioo isPreconnected_Ioo
    isOpen_univ (fun y _ t ht => hode y t ht) hr
    (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨neg_lt_zero.mpr hδ, hδ⟩) (mem_univ x)
  have hinit : (fun y : B.Point => F 0 (j y)) = j := funext (fun y => F.map_zero_apply _)
  rw [hinit, sub_zero] at hp
  have hval := congrArg (fun a => a (fun _ : Fin 1 => v)) hp
  have hi : HasMFDerivAt 𝓘(ℝ, Model (d - 1))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (fun y : B.Point => (y, r)) x
      ((ContinuousLinearMap.id ℝ (Model (d - 1))).prod 0) :=
    (hasMFDerivAt_id x).prodMk (hasMFDerivAt_const r x)
  have hspace := mfderiv_comp_apply (f := fun y : B.Point => (y, r)) (g := c) x
    (hc.mdifferentiableAt (by simp)) hi.mdifferentiableAt v
  rw [hi.mfderiv] at hspace
  change mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) (fun y => F r (j y)) x v =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (v, 0)
      at hspace
  have ht : HasMFDerivAt 𝓘(ℝ, ℝ)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (fun t : ℝ => (x, t)) r
      ((0 : ℝ →L[ℝ] Model (d - 1)).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const x r).prodMk (hasMFDerivAt_id r)
  have htime := mfderiv_comp_apply (f := fun t : ℝ => (x, t)) (g := c) r
    (hc.mdifferentiableAt (by simp)) ht.mdifferentiableAt (1 : ℝ)
  rw [ht.mfderiv] at htime
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun t => F t (j x)) r (1 : ℝ) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (0, 1)
      at htime
  rw [(hode x r hr).mfderiv] at htime
  change (1 : ℝ) • D.neighborhoodStructure.field (F r (j x)) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (0, 1)
      at htime
  rw [one_smul] at htime
  have hsplit : (v, s) = (v, (0 : ℝ)) + s • (0, (1 : ℝ)) := by simp
  change evalOne D.neighborhoodStructure.primitive (F r (j x))
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) c (x, r) (v, s)) = _
  rw [hsplit, map_add, map_smul, ← hspace, ← htime, evalOne_add, evalOne_smul,
    M.evalOne_eq_zero_of_liouvilleEquation _ _ _ (D.neighborhood_contraction _),
    mul_zero, add_zero]
  exact hval

set_option backward.isDefEq.respectTransparency false in
/-- A compact Liouville domain produces a two-sided smooth open boundary
collar with the exact domain side and exponential primitive on that same
collar. The ambient presentation is the canonical symplectic neighborhood.
The auxiliary action is Liouville only on the displayed time strip. -/
theorem exists_liouville_collar {d : ℕ} (D : LiouvilleDomain d) :
    ∃ (δ : ℝ) (F : Flow ℝ D.neighborhoodDomain.extension.Point),
      0 < δ ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × D.neighborhoodDomain.extension.Point => F p.1 p.2) ∧
      (∀ x : D.neighborhoodDomain.boundary.Point, ∀ t ∈ Ioo (-δ) δ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
          (fun s => F s (D.neighborhoodDomain.boundaryInclusion.map x)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (D.neighborhoodStructure.field
            (F t (D.neighborhoodDomain.boundaryInclusion.map x))))) ∧
      InjOn (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
        F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, Model d) ∞ (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
          F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ) ∧
      Topology.IsOpenEmbedding (fun p : {p : D.neighborhoodDomain.boundary.Point × ℝ //
          p ∈ univ ×ˢ Ioo (-δ) δ} =>
        F p.val.2 (D.neighborhoodDomain.boundaryInclusion.map p.val.1)) ∧
      (∀ x : D.neighborhoodDomain.boundary.Point, ∀ t ∈ Ioo (-δ) δ,
        F t (D.neighborhoodDomain.boundaryInclusion.map x) ∈
          D.neighborhoodDomain.carrier ↔ t ≤ 0) ∧
      ∀ (x : D.neighborhoodDomain.boundary.Point) (r : ℝ), r ∈ Ioo (-δ) δ →
        ∀ (v : Model (d - 1)) (s : ℝ),
        evalOne D.neighborhoodStructure.primitive
          (F r (D.neighborhoodDomain.boundaryInclusion.map x))
          (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
            (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
              F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (x, r) (v, s)) =
          Real.exp r * evalOne
            (D.domain.boundaryForm D.liouville.primitive) x v := by
  obtain ⟨U, δ, hU, hδ, F, hF, hode, hinj, hdiff, hside⟩ :=
    D.exists_neighborhood_localCollar_with_side
  have hboundary (x : D.neighborhoodDomain.boundary.Point) (t : ℝ)
      (ht : t ∈ Ioo (-δ) δ) :=
    hode _ (hU (D.neighborhoodDomain.boundaryInclusion_mem_carrier x)) t ht
  refine ⟨δ, F, hδ, hF, hboundary, hinj, hdiff, ?_, hside, ?_⟩
  · let C : TopologicalSpace.Opens (D.neighborhoodDomain.boundary.Point × ℝ) :=
      ⟨univ ×ˢ Ioo (-δ) δ, isOpen_univ.prod isOpen_Ioo⟩
    have hloc : IsLocalHomeomorph (fun p : C =>
        F p.val.2 (D.neighborhoodDomain.boundaryInclusion.map p.val.1)) := by
      rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
      exact hdiff.isLocalHomeomorphOn.comp
        C.isOpenEmbedding'.isLocalHomeomorph.isLocalHomeomorphOn (fun p _ => p.property)
    exact hloc.isOpenEmbedding_of_injective (Set.injOn_iff_injective.mp hinj)
  · intro x r hr v s
    rw [← D.neighborhood_boundaryForm]
    exact D.localBoundaryFlow_primitive F hF hδ hboundary x hr v s

end LiouvilleDomain
end FsFltz.Geometry
