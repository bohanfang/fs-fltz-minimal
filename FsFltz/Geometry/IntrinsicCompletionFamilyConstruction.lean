import FsFltz.Geometry.IntrinsicCompletionPrimitiveFamily
import FsFltz.Geometry.IntrinsicCompletionMixedGerms
import FsFltz.Geometry.IntrinsicCompletionFlow

/-!
# Original completion families with their natural mixed-transition germs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The native source hypotheses construct one varying collar, one original
shared quotient and one primitive family. The SAME retained real collar
extension then produces mutually inverse smooth germs for both directions
of the actual interior/cylinder overlap, including at parameter endpoints.

This theorem retains the producer's geometric witnesses and all primitive
and open-cover conclusions, and constructs all-real Liouville flows for
those SAME primitives. It supplies no new assumptions, and does not
claim a global smooth atlas, a completed bundle trivialization or the
correspondence with a previously presented completion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- Original compact native family data produce the actual original
quotient primitives with complete flows, joint cylinder coefficients and
open cover, together with real smooth germs for the natural mixed transitions on those SAME
quotients. All output witnesses come from one source-only construction. -/
theorem exists_native_completionFamily_with_mixed_germs [CompactSpace M]
    (α : Parameter → IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (IntrinsicLiouville.liouvilleVector (α t)
            (IntrinsicLiouville.exteriorDerivative (α t)) x.val))) :
    ∃ (δ : ℝ) (hδ : 0 < δ)
      (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
      (hemb : ∀ t, IsOpenEmbedding
        (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
      (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
        (C t) (Half δ (IntrinsicBoundary.Point k M)))
      (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
        (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
      (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
        ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
          ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
            ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
      (hzero : ∀ t (b : IntrinsicBoundary.Point k M), C t (0, b) = b.val),
    let X := fun t => completionManifold hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t)
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    IsOpenEmbedding (totalCollar c) ∧
      (∀ t b, IsMIntegralCurveOn (fun s => C t (s, b))
        (fun x => -IntrinsicLiouville.liouvilleVector (α t)
          (IntrinsicLiouville.exteriorDerivative (α t)) x) (Ico 0 δ)) ∧
      (∃ lam : ∀ t, (X t).Form 1,
        (∀ t, (X t).IsSmoothForm (lam t)) ∧
        (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
          (fun x => (lam t (original (c t) x)).compContinuousLinearMap
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original (c t)) x)) = α t) ∧
        (∀ t, P.pullback (X t) (cylinder (c t)) (lam t) = cylinderPrimitive δ (α t)) ∧
        (∀ t x, (X t).Nondegenerate ((X t).exteriorDerivative (lam t)) x) ∧
        (∀ t, Nonempty (CompleteLiouvilleFlow (X t) ((X t).liouvilleVector (lam t)))) ∧
        P.IsSmoothIntervalFormFamily (fun t => P.pullback (X t) (cylinder (c t)) (lam t)) ∧
        IsOpenEmbedding (totalCylinder c) ∧
        IsOpenEmbedding (totalInterior c) ∧
        (∀ x : TotalSpace c, (∃ p, totalInterior c p = x) ∨ ∃ p, totalCylinder c p = x) ∧
        (∀ t p, (fiberEquiv c t (cylinder (c t) p)).val = totalCylinder c (t, p))) ∧
      ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
        (eB : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.boundary)
        (cReal : ℝ × (D.boundary.Point × ℝ) → D.extension.Point)
        (J : TopologicalSpace.Opens ℝ),
        ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
        IsClosedEmbedding i ∧
        (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
        IntrinsicLiouville.HasNativeCoordinateExtensions (k := k) D.extension i ∧
        ContMDiff ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model (k + 1)) ∞ cReal ∧
        parameterInterval ⊆ (J : Set ℝ) ∧
        IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞
          (fun p : ℝ × (D.boundary.Point × ℝ) => (p.1, cReal p))
          ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
        (∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
          i (C t p) = cReal (t.val, (eB p.2, -p.1))) ∧
        ∀ (t : Parameter) (p : ℝ × IntrinsicBoundary.Point k M), p.1 ∈ Ioo 0 δ →
          ∃ A : PartialDiffeomorph
              ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)))
              ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
              (ℝ × (ℝ × IntrinsicBoundary.Point k M))
              (ℝ × IntrinsicInterior.Point k M) ∞,
            (t.val, p) ∈ A.source ∧
            (∀ q ∈ A.source, q.2.1 ∈ Ioo 0 δ) ∧
            (∀ q ∈ A.source, (A q).1 = q.1) ∧
            (∀ q ∈ A.target, (A.symm q).1 = q.1) ∧
            (∀ (a : Parameter) q, (a.val, q) ∈ A.source →
              (A (a.val, q)).2.val = C a q) ∧
            (∀ (a : Parameter) (q : Band δ (IntrinsicBoundary.Point k M)),
              (a.val, q.val) ∈ A.source →
              totalInterior c (a, (A (a.val, q.val)).2) = totalCylinder c (a, q)) ∧
            (∀ (a : Parameter) (x : IntrinsicInterior.Point k M), (a.val, x) ∈ A.target →
              ∃ q : Band δ (IntrinsicBoundary.Point k M),
                A.symm (a.val, x) = (a.val, q.val) ∧
                totalCylinder c (a, q) = totalInterior c (a, x)) := by
  obtain ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hode, hlam,
      D, i, eB, cReal, J, hi, hiemb, hbij, hcoord, hc, hJ, hdiff, hsquare⟩ :=
    exists_native_primitiveFamily_with_joint_seam α hα hnd hout
  rcases hlam with ⟨lam, hsmooth, hnative, hcylinder, hnondeg, hfamily,
    hcylEmb, hintEmb, hcover, hfiber⟩
  refine ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hode,
    ⟨lam, hsmooth, hnative, hcylinder, hnondeg, ?_, hfamily, hcylEmb, hintEmb, hcover, hfiber⟩,
    D, i, eB, cReal, J, hi, hiemb, hbij, hcoord, hc, hJ, hdiff, hsquare, ?_⟩
  · intro t
    exact exists_completeLiouvilleFlow hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t) (α t) (hα.slice t) (lam t)
      (hsmooth t) (hnondeg t) (hcylinder t)
  · exact exists_joint_mixed_transition_germ C
      (fun t b s hs => hboundary t ⟨(s, b), hs, mem_univ _⟩)
      D i hi hiemb.injective hbij eB cReal J hJ hdiff hsquare

end FsFltz.Geometry.IntrinsicCompletionGluing
