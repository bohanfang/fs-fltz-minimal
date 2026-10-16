import FsFltz.Geometry.NativeCompactLiouvilleRestriction
import FsFltz.Geometry.IntrinsicNativeIdentificationFamily

/-!
# Native Liouville restriction on a fixed compact presentation

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160,
`def:chain`, lines 163–169, and `sec:lean`, lines 783–814. An actual
domain presentation transports the target primitive to the fixed source
carrier. Its smooth ambient map supplies native coordinate and scalar
germs, and its full differential retains the target Liouville laws.

No new domain-law record or geometric existence assertion is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.DomainPresentationEquiv

variable {k : ℕ} {S : CompactDomain (k + 1)} {D : LiouvilleDomain (k + 1)}
  (h : DomainPresentationEquiv S D.domain)

/-- The actual presentation retains the native boundary locus. -/
theorem nativePointDiffeomorph_boundary_iff (x : S.Point) :
    (𝓡∂ (k + 1)).IsBoundaryPoint (h.nativePointDiffeomorph x) ↔
      (𝓡∂ (k + 1)).IsBoundaryPoint x := by
  change x ∈ h.nativePointDiffeomorph ⁻¹' (𝓡∂ (k + 1)).boundary D.domain.Point ↔
    x ∈ (𝓡∂ (k + 1)).boundary S.Point
  rw [Diffeomorph.preimage_boundary (by simp : (∞ : WithTop ℕ∞) ≠ 0)]

/-- An encoded presentation gives a native presentation of its actual
pulled-back primitive on the fixed source carrier, retaining the exact target
domain and the prescribed native compact diffeomorphism. -/
def nativeLiouvillePresentation :
    IntrinsicLiouville.NativeLiouvillePresentation
      (S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
        D.liouville.primitive)) := by
  let i : S.Point → D.domain.extension.Point := fun x => h.extensionEquiv x.val
  have hp (x : S.Point) : (D.liouville.primitive (h.nativePointDiffeomorph x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (fun y => (h.nativePointDiffeomorph y).val) x) =
      S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
        D.liouville.primitive) x := by
    have hc := mfderiv_comp (f := (Subtype.val : S.Point → S.extension.Point))
      (g := h.extensionEquiv) x
      (h.extensionEquiv.contMDiff.mdifferentiableAt (by simp))
      (S.contMDiff_subtype_val.mdifferentiableAt (by simp))
    change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x = _ at hc
    change (D.liouville.primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = _
    rw [hc]
    ext vs
    rfl
  have hcoord : IntrinsicLiouville.HasNativeCoordinateExtensions (k := k)
      D.domain.extension i :=
    IntrinsicLiouville.HasNativeCoordinateExtensions.of_smooth_square
      S.extension D.domain.extension (Subtype.val : S.Point → S.extension.Point) i
      S.hasNativeCoordinateExtensions_subtype_val h.extensionEquiv.symm
      h.extensionEquiv.symm.contMDiff (fun _ => h.extensionEquiv.symm_apply_apply _)
  exact IntrinsicLiouville.NativeLiouvillePresentation.of_endpoint _ D
    h.nativePointDiffeomorph hp hcoord

@[simp] theorem nativeLiouvillePresentation_domain :
    h.nativeLiouvillePresentation.domain = D := rfl

@[simp] theorem nativeLiouvillePresentation_inclusion (x : S.Point) :
    h.nativeLiouvillePresentation.inclusion x = h.extensionEquiv x.val := rfl

/-- Nondegeneracy of the actual fixed-carrier pullback includes every
native boundary tangent. -/
theorem native_restricted_nondegenerate (x : S.Point) :
    IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative
        (S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
          D.liouville.primitive))) x :=
  h.nativeLiouvillePresentation.native_nondegenerate x

/-- The target field is exactly the pushforward of the canonical field
of the native primitive on the fixed compact presentation. -/
theorem native_restricted_field_inclusion (x : S.Point) :
    D.liouville.field (h.extensionEquiv x.val) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (fun y : S.Point => h.extensionEquiv y.val) x
        (IntrinsicLiouville.liouvilleVector
          (S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
            D.liouville.primitive))
          (IntrinsicLiouville.exteriorDerivative
            (S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
              D.liouville.primitive))) x) :=
  h.nativeLiouvillePresentation.field_inclusion x

/-- The target's actual defining function, pulled through the prescribed
presentation, defines the native boundary of the fixed source carrier and
has the same strict outward derivative. -/
theorem native_restricted_definingFunction_laws
    (b : IntrinsicBoundary.Point k S.Point) :
    let hfrontier := (D.domain.isBoundaryPoint_iff_frontier
      (h.nativePointDiffeomorph b.val)).mp
        ((h.nativePointDiffeomorph_boundary_iff b.val).mpr b.property)
    let R := D.domain.defining (h.extensionEquiv b.val.val) hfrontier
    let rho := R.rho ∘ h.extensionEquiv ∘ (Subtype.val : S.Point → S.extension.Point)
    ∃ beta : Model (k + 1) → ℝ,
      rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
      (∀ᶠ y in 𝓝 b.val, rho y = 0 ↔ (𝓡∂ (k + 1)).IsBoundaryPoint y) ∧
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val ≠ 0 ∧
      ContDiffAt ℝ ∞ beta
        ((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1)) b.val) ∧
      beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1)) b.val)]
        (rho ∘ ((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1))).symm) ∧
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val
        (IntrinsicLiouville.liouvilleVector
          (S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
            D.liouville.primitive))
          (IntrinsicLiouville.exteriorDerivative
            (S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
              D.liouville.primitive))) b.val)) := by
  let hfrontier := (D.domain.isBoundaryPoint_iff_frontier
    (h.nativePointDiffeomorph b.val)).mp
      ((h.nativePointDiffeomorph_boundary_iff b.val).mpr b.property)
  let R := D.domain.defining (h.extensionEquiv b.val.val) hfrontier
  let i : S.Point → D.domain.extension.Point := fun x => h.extensionEquiv x.val
  let rho := R.rho ∘ i
  let e := (IntrinsicBoundary.chartAt (k := k) b).ambient
  have hbs : b.val ∈ e.source := by
    have hb := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt (k := k) b).source_eq] at hb
  have hs : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞
      (R.rho ∘ h.extensionEquiv) (h.extensionEquiv ⁻¹' R.neighbourhood) :=
    R.smooth_rho.comp h.extensionEquiv.contMDiff.contMDiffOn (fun _ hy => hy)
  obtain ⟨beta, U, hU, hbU, hbeta, heq⟩ := S.exists_scalar_restriction_germ
    (R.rho ∘ h.extensionEquiv) (h.extensionEquiv ⁻¹' R.neighbourhood)
      (R.open_neighbourhood.preimage h.extensionEquiv.continuous) hs e
        (IntrinsicBoundary.chartAt (k := k) b).mem_atlas b.val hbs R.mem_neighbourhood
  have hR : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ R.rho (i b.val) :=
    R.smooth_rho.contMDiffAt (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)
  have hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i :=
    h.extensionEquiv.contMDiff.comp S.contMDiff_subtype_val
  have hchain := mfderiv_comp (f := i) (g := R.rho) b.val
    (hR.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  change ∃ beta : Model (k + 1) → ℝ, _
  refine ⟨beta, (R.zero_level (i b.val) R.mem_neighbourhood).mp hfrontier,
    ?_, ?_, ?_, hbeta.contDiffAt (hU.mem_nhds hbU), heq, ?_⟩
  · filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds
      (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)] with y hy
    exact (R.sublevel (i y) hy).mp ((h.mem_carrier_iff y.val).mpr y.property)
  · filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds
      (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)] with y hy
    exact ((R.zero_level (i y) hy).symm).trans
      ((D.domain.isBoundaryPoint_iff_frontier (h.nativePointDiffeomorph y)).symm.trans
        (h.nativePointDiffeomorph_boundary_iff y))
  · change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (R.rho ∘ i) b.val ≠ 0
    intro hz
    apply R.regular
    ext v
    obtain ⟨u, rfl⟩ := (h.nativeLiouvillePresentation.tangent_bijective b.val).2 v
    have hcv := congrArg (fun A => A u) hchain
    rw [hz] at hcv
    exact hcv.symm
  · change 0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (R.rho ∘ i) b.val
      (IntrinsicLiouville.liouvilleVector _ _ b.val))
    rw [hchain]
    change 0 < (show ℝ from mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) R.rho (i b.val)
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i b.val
        (IntrinsicLiouville.liouvilleVector _ _ b.val)))
    have hf := h.native_restricted_field_inclusion b.val
    change D.liouville.field (i b.val) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i b.val
        (IntrinsicLiouville.liouvilleVector _ _ b.val) at hf
    rw [← hf]
    exact D.liouville.outward (i b.val) hfrontier

/-- The actual primitive pulled onto a fixed compact presentation has the
complete native Liouville laws, including the exact local boundary zero set. -/
theorem native_restricted_liouville_laws :
    let alpha := S.restrictForm (S.extension.pullback D.domain.extension h.extensionEquiv
      D.liouville.primitive)
    IntrinsicLiouville.IsLocallyExtendibleForm alpha ∧
    IntrinsicLiouville.HasExteriorDerivative alpha (IntrinsicLiouville.exteriorDerivative alpha) ∧
    IntrinsicLiouville.IsLocallyExtendibleForm (IntrinsicLiouville.exteriorDerivative alpha) ∧
    IntrinsicLiouville.exteriorDerivative (IntrinsicLiouville.exteriorDerivative alpha) = 0 ∧
    (∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative alpha) x) ∧
    IntrinsicLiouville.Contraction alpha (IntrinsicLiouville.exteriorDerivative alpha)
      (IntrinsicLiouville.liouvilleVector alpha (IntrinsicLiouville.exteriorDerivative alpha)) ∧
    ∀ b : IntrinsicBoundary.Point k S.Point,
      ∃ (rho : S.Point → ℝ) (beta : Model (k + 1) → ℝ),
        rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
        (∀ᶠ y in 𝓝 b.val, rho y = 0 ↔ (𝓡∂ (k + 1)).IsBoundaryPoint y) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1)) b.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1)) b.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt (k := k) b).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val
          (IntrinsicLiouville.liouvilleVector alpha
            (IntrinsicLiouville.exteriorDerivative alpha) b.val)) := by
  have hp := S.extension.isSmoothForm_pullback_one D.domain.extension
    h.extensionEquiv.toContMDiffMap D.liouville.primitive D.liouville.smooth_primitive
  have halpha := S.isLocallyExtendibleForm_restrictForm _ hp
  refine ⟨halpha, IntrinsicLiouville.hasExteriorDerivative_exteriorDerivative _ halpha,
    IntrinsicLiouville.isLocallyExtendibleForm_exteriorDerivative _ halpha,
    IntrinsicLiouville.exteriorDerivative_exteriorDerivative _ halpha,
    h.native_restricted_nondegenerate,
    IntrinsicLiouville.contraction_liouvilleVector _ _ h.native_restricted_nondegenerate, ?_⟩
  intro b
  exact ⟨_, h.native_restricted_definingFunction_laws b⟩

end FsFltz.Geometry.DomainPresentationEquiv

namespace FsFltz.Geometry

private theorem native_presented_slice_laws_reindex {d k : ℕ}
    (S : CompactDomain d) (D : LiouvilleDomain d)
    (h : DomainPresentationEquiv S D.domain)
    (eta₀ : Parameter → S.extension.Form 1) (t : Parameter)
    (heta : eta₀ t = S.extension.pullback D.domain.extension h.extensionEquiv D.liouville.primitive)
    (hdim : d = k + 1) :
    let S' : CompactDomain (k + 1) := hdim ▸ S
    letI := CompactDomain.halfSpaceChartedSpace S'
    letI := CompactDomain.isManifold_halfSpace S'
    let eta : Parameter → S'.extension.Form 1 :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ S).extension.Form 1) eta₀
    let alpha := S'.restrictForm (eta t)
    (∀ x, @IntrinsicLiouville.Nondegenerate k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (@IntrinsicLiouville.exteriorDerivative k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') 1 alpha) x) ∧
    ∀ b : (@IntrinsicBoundary.Point k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S')),
      ∃ (rho : S'.Point → ℝ) (beta : Model (k + 1) → ℝ),
        rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
        (∀ᶠ y in 𝓝 b.val, rho y = 0 ↔ @ModelWithCorners.IsBoundaryPoint ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') y) ∧
        @mfderiv ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') ℝ inferInstance inferInstance ℝ inferInstance 𝓘(ℝ, ℝ) ℝ inferInstance inferInstance rho b.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((@IntrinsicBoundary.Chart.ambient k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (@IntrinsicBoundary.chartAt k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (CompactDomain.isManifold_halfSpace S') b)).extend (𝓡∂ (k + 1)) b.val) ∧
        beta =ᶠ[𝓝[((@IntrinsicBoundary.Chart.ambient k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (@IntrinsicBoundary.chartAt k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (CompactDomain.isManifold_halfSpace S') b)).extend (𝓡∂ (k + 1))).target]
          ((@IntrinsicBoundary.Chart.ambient k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (@IntrinsicBoundary.chartAt k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (CompactDomain.isManifold_halfSpace S') b)).extend (𝓡∂ (k + 1)) b.val)]
          (rho ∘ ((@IntrinsicBoundary.Chart.ambient k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (@IntrinsicBoundary.chartAt k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') (CompactDomain.isManifold_halfSpace S') b)).extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from @mfderiv ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') ℝ inferInstance inferInstance ℝ inferInstance 𝓘(ℝ, ℝ) ℝ inferInstance inferInstance rho b.val
          (@IntrinsicLiouville.liouvilleVector k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') alpha
            (@IntrinsicLiouville.exteriorDerivative k S'.Point inferInstance (CompactDomain.halfSpaceChartedSpace S') 1 alpha) b.val)) := by
  cases hdim
  obtain ⟨_, _, _, _, hnd, _, hout⟩ := h.native_restricted_liouville_laws
  simpa only [heta] using And.intro hnd hout

namespace PairDeformation

/-- Ambient family laws on the exact fixed source compact carrier.
Joint real primitive germs and all slice nondegeneracy/outward laws follow
from the encoded deformation and its prescribed presentations. -/
theorem ambientPrimitive_native_slice_laws {n k : ℕ} (Q : PairDeformation n)
    (hdim : 2 * n = k + 1) :
    let S₀ := (Q.pair parameterZero).ambientDomain.domain
    let eta₀ : Parameter → S₀.extension.Form 1 := fun t =>
      S₀.extension.pullback (Q.pair t).ambientDomain.domain.extension
        (Q.ambientPresentation t).extensionEquiv (Q.pair t).ambientDomain.liouville.primitive
    let S : CompactDomain (k + 1) := hdim ▸ S₀
    letI := CompactDomain.halfSpaceChartedSpace S
    letI := CompactDomain.isManifold_halfSpace S
    let eta : Parameter → S.extension.Form 1 :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ S₀).extension.Form 1) eta₀
    let alpha := fun t => S.restrictForm (eta t)
    @IntrinsicLiouville.IsLocallyExtendibleFormFamily k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) 1 alpha ∧
    ∀ t, (∀ x, @IntrinsicLiouville.Nondegenerate k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicLiouville.exteriorDerivative k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) 1 (alpha t)) x) ∧
    ∀ b : (@IntrinsicBoundary.Point k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S)),
      ∃ (rho : S.Point → ℝ) (beta : Model (k + 1) → ℝ),
        rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
        (∀ᶠ y in 𝓝 b.val, rho y = 0 ↔ @ModelWithCorners.IsBoundaryPoint ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) y) ∧
        @mfderiv ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) ℝ inferInstance inferInstance ℝ inferInstance 𝓘(ℝ, ℝ) ℝ inferInstance inferInstance rho b.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1)) b.val) ∧
        beta =ᶠ[𝓝[((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1))).target]
          ((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1)) b.val)]
          (rho ∘ ((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from @mfderiv ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) ℝ inferInstance inferInstance ℝ inferInstance 𝓘(ℝ, ℝ) ℝ inferInstance inferInstance rho b.val
          (@IntrinsicLiouville.liouvilleVector k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (alpha t)
            (@IntrinsicLiouville.exteriorDerivative k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) 1 (alpha t)) b.val)) := by
  refine ⟨Q.ambientPrimitive_native_extendible hdim, ?_⟩
  intro t
  exact native_presented_slice_laws_reindex
    (Q.pair parameterZero).ambientDomain.domain (Q.pair t).ambientDomain
    (Q.ambientPresentation t)
    (fun s => (Q.pair parameterZero).ambientDomain.domain.extension.pullback
      (Q.pair s).ambientDomain.domain.extension (Q.ambientPresentation s).extensionEquiv
      (Q.pair s).ambientDomain.liouville.primitive) t rfl hdim

/-- Positive-dimensional ribbon family laws on the exact fixed source compact carrier.
Joint real primitive germs and all slice nondegeneracy/outward laws follow
from the encoded deformation and its prescribed presentations. -/
theorem ribbonPrimitive_native_slice_laws {n k : ℕ} (Q : PairDeformation n)
    (hdim : 2 * n - 2 = k + 1) :
    let S₀ := (Q.pair parameterZero).ribbonDomain.domain
    let eta₀ : Parameter → S₀.extension.Form 1 := fun t =>
      S₀.extension.pullback (Q.pair t).ribbonDomain.domain.extension
        (Q.ribbonPresentation t).extensionEquiv (Q.pair t).ribbonDomain.liouville.primitive
    let S : CompactDomain (k + 1) := hdim ▸ S₀
    letI := CompactDomain.halfSpaceChartedSpace S
    letI := CompactDomain.isManifold_halfSpace S
    let eta : Parameter → S.extension.Form 1 :=
      hdim.rec (motive := fun _ h => Parameter → (h ▸ S₀).extension.Form 1) eta₀
    let alpha := fun t => S.restrictForm (eta t)
    @IntrinsicLiouville.IsLocallyExtendibleFormFamily k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) 1 alpha ∧
    ∀ t, (∀ x, @IntrinsicLiouville.Nondegenerate k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicLiouville.exteriorDerivative k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) 1 (alpha t)) x) ∧
    ∀ b : (@IntrinsicBoundary.Point k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S)),
      ∃ (rho : S.Point → ℝ) (beta : Model (k + 1) → ℝ),
        rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
        (∀ᶠ y in 𝓝 b.val, rho y = 0 ↔ @ModelWithCorners.IsBoundaryPoint ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) y) ∧
        @mfderiv ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) ℝ inferInstance inferInstance ℝ inferInstance 𝓘(ℝ, ℝ) ℝ inferInstance inferInstance rho b.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1)) b.val) ∧
        beta =ᶠ[𝓝[((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1))).target]
          ((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1)) b.val)]
          (rho ∘ ((@IntrinsicBoundary.Chart.ambient k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (@IntrinsicBoundary.chartAt k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (CompactDomain.isManifold_halfSpace S) b)).extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from @mfderiv ℝ inferInstance (Model (k + 1)) inferInstance inferInstance (EuclideanHalfSpace (k + 1)) inferInstance (𝓡∂ (k + 1)) S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) ℝ inferInstance inferInstance ℝ inferInstance 𝓘(ℝ, ℝ) ℝ inferInstance inferInstance rho b.val
          (@IntrinsicLiouville.liouvilleVector k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) (alpha t)
            (@IntrinsicLiouville.exteriorDerivative k S.Point inferInstance (CompactDomain.halfSpaceChartedSpace S) 1 (alpha t)) b.val)) := by
  refine ⟨Q.ribbonPrimitive_native_extendible hdim, ?_⟩
  intro t
  exact native_presented_slice_laws_reindex
    (Q.pair parameterZero).ribbonDomain.domain (Q.pair t).ribbonDomain
    (Q.ribbonPresentation t)
    (fun s => (Q.pair parameterZero).ribbonDomain.domain.extension.pullback
      (Q.pair s).ribbonDomain.domain.extension (Q.ribbonPresentation s).extensionEquiv
      (Q.pair s).ribbonDomain.liouville.primitive) t rfl hdim

end PairDeformation
end FsFltz.Geometry
