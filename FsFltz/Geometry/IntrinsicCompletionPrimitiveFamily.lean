import FsFltz.Geometry.IntrinsicCompletionFamilyCharts
import FsFltz.Geometry.IntrinsicCompletionCylinderFamily
import FsFltz.Geometry.IntrinsicCompletionPrimitive
import FsFltz.Geometry.IntrinsicNativeJointCollar

/-!
# Vertical primitive regularity on the original varying quotient seams

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158,
`def:chain`, lines 163–169, and `sec:lean`, lines 788–814.
Original native primitive germs and the actual varying inward Liouville
collars construct the original quotient primitives. Their spatial pullbacks
to the same shared cylinder chart are jointly smooth across every seam.
The parameter is an index, never an extra one-form tangent argument.

All slice collars may vary. The first theorem accepts their raw joint
embedding explicitly; the source-only consumer derives these collars from
the native primitive family and its outward Liouville field. Completed
primitive smoothness, a completed family, and a comparison map are not
inputs. Global joint regularity and the interior/cylinder mixed transitions
on the entire total space remain separate foundations.
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
  (hzero : ∀ t (b : IntrinsicBoundary.Point k M), C t (0, b) = b.val)

/-- The primitive selected on each original quotient has joint spatial
coefficients in its actual shared cylinder chart, including at radius zero.
It retains the entire native primitive, exact cylinder formula and
nondegenerate differential on those SAME original quotients. -/
theorem exists_primitiveFamily_with_joint_seam
    (α : Parameter → IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (α t)) x)
    (Z : (t : Parameter) → (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : ∀ t, IntrinsicLiouville.Contraction (α t)
      (IntrinsicLiouville.exteriorDerivative (α t)) (Z t))
    (hode : ∀ t b, IsMIntegralCurveOn (fun s => C t (s, b))
      (fun x => -Z t x) (Ico 0 δ))
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))) :
    let X := fun t => completionManifold hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t)
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    ∃ lam : ∀ t, (X t).Form 1,
      (∀ t, (X t).IsSmoothForm (lam t)) ∧
      (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
        (fun x => (lam t (original (c t) x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original (c t)) x)) = α t) ∧
      (∀ t, P.pullback (X t) (cylinder (c t)) (lam t) = cylinderPrimitive δ (α t)) ∧
      (∀ t x, (X t).Nondegenerate ((X t).exteriorDerivative (lam t)) x) ∧
      P.IsSmoothIntervalFormFamily (fun t => P.pullback (X t) (cylinder (c t)) (lam t)) ∧
      IsOpenEmbedding (totalCylinder c) ∧
      IsOpenEmbedding (totalInterior c) ∧
      (∀ x : TotalSpace c, (∃ p, totalInterior c p = x) ∨ ∃ p, totalCylinder c p = x) ∧
      (∀ t p, (fiberEquiv c t (cylinder (c t) p)).val = totalCylinder c (t, p)) := by
  let X := fun t => completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  have hex (t : Parameter) := exists_smooth_symplectic_primitive hδ (C t) (hemb t)
    (hC t) (hboundary t) (hinv t) (hzero t) (α t) (hα.slice t)
    (hnd t) (Z t) (hZ t) (hode t)
  choose lam hlam hfinite hnative hcylinder hnondeg using hex
  refine ⟨lam, hlam, hnative, hcylinder, hnondeg, ?_,
    isOpenEmbedding_totalCylinder c hjoint,
    isOpenEmbedding_totalInterior hδ c (fun t b => hzero t b) hjoint,
    totalInterior_cylinder_cover hδ c (fun t b => hzero t b), ?_⟩
  · have heq : (fun t => P.pullback (X t) (cylinder (c t)) (lam t)) =
        (fun t => cylinderPrimitive δ (α t)) := funext hcylinder
    rw [heq]
    exact isSmoothIntervalFormFamily_cylinderPrimitive δ α hα
  · intro t p
    exact sliceIn_cylinder c t p

/-- The original compact native family hypotheses produce the varying
quotients, their SAME primitive family, actual open cover and joint spatial
cylinder coefficients. The SAME real collar extension is retained for
constructing the natural mixed-transition germs. No completed regularity,
collar, quotient presentation or comparison is an input. -/
theorem exists_native_primitiveFamily_with_joint_seam [CompactSpace M]
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
        ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
          i (C t p) = cReal (t.val, (eB p.2, -p.1)) := by
  obtain ⟨δ₀, C₀, hδ₀, hjoint, hC₀, hzero₀, hboundaryRaw, hemb₀, hinv₀,
      hode, hext⟩ := IntrinsicLiouville.exists_uniform_native_joint_collar α hα hnd hout
  have hboundary₀ (t : Parameter) (p : Half δ₀ (IntrinsicBoundary.Point k M)) :
      (𝓡∂ (k + 1)).IsBoundaryPoint (C₀ t p.val) ↔ p.val.1 = 0 :=
    hboundaryRaw t p.val.2 p.val.1 p.property.1
  refine ⟨δ₀, hδ₀, C₀, hemb₀, hC₀, hboundary₀, hinv₀, hzero₀, hjoint, hode, ?_, hext⟩
  exact exists_primitiveFamily_with_joint_seam hδ₀ C₀ hemb₀ hC₀ hboundary₀
    hinv₀ hzero₀ α hα hnd
    (fun t => IntrinsicLiouville.liouvilleVector (α t)
      (IntrinsicLiouville.exteriorDerivative (α t)))
    (fun t => IntrinsicLiouville.contraction_liouvilleVector (α t)
      (IntrinsicLiouville.exteriorDerivative (α t)) (hnd t)) hode hjoint

end FsFltz.Geometry.IntrinsicCompletionGluing
