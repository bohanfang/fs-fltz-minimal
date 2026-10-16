import FsFltz.Geometry.IntrinsicNativeCompletionCoefficientDescent

/-!
# Spatial nondegeneracy of the original interior inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The original interior inverse germ is a
composition of the actual native relabeling inverse and the reference
inclusion inverse. Its spatial derivative is invertible on the same
real-open neighborhood, with exact original interval values retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicInterior

/-- A native diffeomorphism restricts to the intrinsic interiors. -/
def restrictDiffeomorph {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M]
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞) :
    Diffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (Point k M) (Point k M) ∞ where
  toFun x := ⟨e x.val, (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
    (e.isLocalDiffeomorph x.val)).mp x.property⟩
  invFun x := ⟨e.symm x.val, (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
    (e.symm.isLocalDiffeomorph x.val)).mp x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  contMDiff_toFun := contMDiff_iff_val.mpr (e.contMDiff.comp contMDiff_val)
  contMDiff_invFun := contMDiff_iff_val.mpr (e.symm.contMDiff.comp contMDiff_val)

end FsFltz.Geometry.IntrinsicInterior

namespace FsFltz.Geometry.PairDeformation
open IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair t).ambientDomain.domain.Point ∞)
  (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary)
  (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
  (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))

include hdim hR in
/-- The original compact-interior inverse has a real smooth spatial germ,
using the original native relabeling family and the fixed reference inclusion.
Its spatial differential is invertible throughout the same real-open neighborhood,
and its restriction to every nearby interval point is the original total inverse. -/
theorem exists_ambientNativeTotalEquiv_symm_realInteriorGerm_verticalDerivative
    (t : Parameter) (u : IntrinsicInterior.Point k M) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.ambientNativeInteriorReferenceMap (e parameterZero) u) ∈ U ∧
      ∃ g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          𝓘(ℝ, Model (k + 1)) ∞ g U ∧
        (g (t.val, Q.ambientNativeInteriorReferenceMap (e parameterZero) u)).val =
          (R t.val).symm u.val ∧
        (∀ z ∈ U, (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
          (fun y => g (z.1, y)) z.2).IsInvertible) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
            totalInterior (fun t p => C t p.val) (s, g (s.val, y)) := by
  let A := Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend
  let f := Q.ambientNativeInteriorReferenceMap (e parameterZero)
  let l := Q.isLocalDiffeomorph_ambientNativeInteriorReferenceMap hdim (e parameterZero) u
  let ri : ℝ × IntrinsicInterior.Point k M → IntrinsicInterior.Point k M :=
    fun p => ⟨(R p.1).symm p.2.val,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((R p.1).symm.isLocalDiffeomorph p.2.val)).mp p.2.property⟩
  have hri : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (k + 1)) ∞ ri := by
    apply IntrinsicInterior.contMDiff_iff_val.mpr
    exact hR.2.comp (contMDiff_id.prodMap IntrinsicInterior.contMDiff_val)
  let U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point) :=
    Prod.snd ⁻¹' l.localInverse.source
  have hU : IsOpen U := l.localInverse.open_source.preimage continuous_snd
  let g := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
    ri (z.1, l.localInverse z.2)
  have hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ g U := by
    apply hri.comp_contMDiffOn
    exact contMDiffOn_fst.prodMk
      (l.localInverse_contMDiffOn.comp contMDiffOn_snd (fun _ hz => hz))
  refine ⟨U, hU, l.localInverse_mem_source, g, hg, ?_, ?_, ?_⟩
  · change (R t.val).symm (l.localInverse (f u)).val = (R t.val).symm u.val
    rw [l.localInverse_left_inv l.localInverse_mem_target]
  · intro z hz
    let d := IntrinsicInterior.restrictDiffeomorph ((R z.1).symm)
    have hl := l.localInverse.isLocalDiffeomorphAt _ _ _ hz
    have hd := d.isLocalDiffeomorph (l.localInverse z.2)
    have hcomp := IsLocalDiffeomorphAt.comp 𝓘(ℝ, Model (k + 1))
      (IntrinsicInterior.Point k M) hl hd
    exact hcomp.isInvertible_mfderiv (by simp)
  · intro s y hy
    apply A.injective
    rw [A.apply_symm_apply]
    apply Prod.ext
    · rfl
    · change y = q (original (totalCollar (fun t p => C t p.val))
        (s, (R s.val).symm (l.localInverse y).val))
      rw [hqnative, Q.ambientNativeReferenceMap_eq_compact e R hsquareA]
      change y = Q.source.ambientCompletion.inclusion.map
        (e parameterZero (R s.val ((R s.val).symm (l.localInverse y).val))).val
      rw [(R s.val).apply_symm_apply]
      exact (l.localInverse_right_inv hy).symm


end FsFltz.Geometry.PairDeformation
