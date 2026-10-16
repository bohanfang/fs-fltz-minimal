import FsFltz.Geometry.NativeCompactFormRestriction
import FsFltz.Geometry.IntrinsicNativeEndpointPresentation
import FsFltz.Geometry.IntrinsicPresentationCollarComparison
import FsFltz.Geometry.IntrinsicExteriorDerivativeRegularity

/-!
# Native Liouville laws on the actual compact carrier

Source: `geoemtric-part-fsf.tex`, conventions 119–130, `def:pair`,
132–160, and `sec:lean`, 783–814. The encoded domain's extended charts
produce actual native coordinate and defining-function germs. The primitive
is the differential pullback through the literal subtype inclusion, and its
full tangent Liouville laws follow from the same encoded domain.

This is a positive-dimensional restriction theorem. It supplies no geometric
comparison chain, endpoint core equality, or completion marking.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

namespace CompactDomain

variable {k : ℕ} (D : CompactDomain (k + 1))

/-- The actual compact inclusion has smooth open extensions of its native
source coordinates. These are the forward maps of the existing extended
half-space charts, with literal agreement on the whole carrier patch. -/
theorem hasNativeCoordinateExtensions_subtype_val :
    IntrinsicLiouville.HasNativeCoordinateExtensions (k := k) D.extension
      (Subtype.val : D.Point → D.extension.Point) := by
  intro x
  let c := D.halfSpaceChartAt x
  refine ⟨c.chart, c.extension.source, c.extension, ⟨c, rfl⟩,
    c.extension.open_source, ?_, c.extension.contMDiffOn_toFun, ?_⟩
  · have hx := D.mem_halfSpaceChartAt_source x
    rwa [c.source_eq] at hx
  · intro y hy
    have hys : y ∈ c.chart.source := by rwa [c.source_eq]
    refine ⟨hys, ?_⟩
    change c.extension y.val = (c.chart y).val
    exact (c.toFun_eq y hys).symm

/-- A scalar smooth on an actual ambient open neighborhood has real open
coordinate germs after restriction to the compact carrier. The germ is
the scalar composed with the specified smooth ambient inverse chart. -/
theorem exists_scalar_restriction_germ
    (rho : D.extension.Point → ℝ) (V : Set D.extension.Point) (hV : IsOpen V)
    (hrho : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ rho V)
    (e : OpenPartialHomeomorph D.Point (EuclideanHalfSpace (k + 1)))
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) D.Point)
    (x : D.Point) (hx : x ∈ e.source) (hxV : x.val ∈ V) :
    ∃ (beta : Model (k + 1) → ℝ) (U : Set (Model (k + 1))),
      IsOpen U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧ ContDiffOn ℝ ∞ beta U ∧
      beta =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
        (e.extend (𝓡∂ (k + 1)) x)]
        ((rho ∘ (Subtype.val : D.Point → D.extension.Point)) ∘
          (e.extend (𝓡∂ (k + 1))).symm) := by
  obtain ⟨c, rfl⟩ := he
  let U := c.extension.target ∩ c.extension.invFun ⁻¹' V
  have hU : IsOpen U :=
    c.extension.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage
      c.extension.open_target hV
  have hxt : c.chart.extend (𝓡∂ (k + 1)) x ∈
      (c.chart.extend (𝓡∂ (k + 1))).target :=
    (c.chart.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [c.chart.extend_source] using hx)
  have hxx : c.extension.invFun (c.chart.extend (𝓡∂ (k + 1)) x) = x.val := by
    rw [← c.val_extend_symm D hxt, c.chart.extend_left_inv hx]
  refine ⟨rho ∘ c.extension.invFun, U, hU,
    ⟨(c.extend_target_eq D ▸ hxt).1, by simpa only [mem_preimage, hxx] using hxV⟩,
    ?_, ?_⟩
  · exact (hrho.comp (c.extension.contMDiffOn_invFun.mono inter_subset_left)
      (fun _ hz => hz.2)).contDiffOn
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Function.comp_apply, c.val_extend_symm D hy]

end CompactDomain

namespace LiouvilleDomain

variable {k : ℕ} (D : LiouvilleDomain (k + 1))

/-- The original encoded endpoint presents its literal native compact
carrier. No new domain, equivalence, primitive or extension is selected. -/
def nativePresentation :
    IntrinsicLiouville.NativeLiouvillePresentation
      (D.domain.restrictForm D.liouville.primitive) :=
  IntrinsicLiouville.NativeLiouvillePresentation.of_endpoint
    (D.domain.restrictForm D.liouville.primitive) D (Diffeomorph.refl _ _ ∞)
    (fun _ => rfl) D.domain.hasNativeCoordinateExtensions_subtype_val

@[simp] theorem nativePresentation_domain : D.nativePresentation.domain = D := rfl

@[simp] theorem nativePresentation_inclusion (x : D.domain.Point) :
    D.nativePresentation.inclusion x = x.val := rfl

/-- The full native differential is exactly the restricted ambient
exterior derivative, at interior and boundary points. -/
theorem exteriorDerivative_restrict_primitive :
    IntrinsicLiouville.exteriorDerivative (D.domain.restrictForm D.liouville.primitive) =
      D.domain.restrictForm (D.domain.extension.exteriorDerivative D.liouville.primitive) :=
  D.nativePresentation.differential.symm

/-- Native symplectic nondegeneracy on every full tangent space follows
from the encoded domain's symplectic law and the actual inclusion. -/
theorem native_nondegenerate (x : D.domain.Point) :
    IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (D.domain.restrictForm D.liouville.primitive)) x :=
  D.nativePresentation.native_nondegenerate x

/-- The canonical native Liouville vector is carried to the encoded field
by the full differential of the literal inclusion. -/
theorem native_field_inclusion (x : D.domain.Point) :
    D.liouville.field x.val =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (Subtype.val : D.domain.Point → D.domain.extension.Point) x
        (IntrinsicLiouville.liouvilleVector (D.domain.restrictForm D.liouville.primitive)
          (IntrinsicLiouville.exteriorDerivative
            (D.domain.restrictForm D.liouville.primitive)) x) :=
  D.nativePresentation.field_inclusion x

/-- The stored ambient defining function restricts to a genuine native
defining function. Its real chart germ, regular differential and strict
outward derivative are consequences of the original domain laws. -/
theorem native_definingFunction_laws
    (b : IntrinsicBoundary.Point k D.domain.Point) :
    let hfrontier := (D.domain.isBoundaryPoint_iff_frontier b.val).mp b.property
    let R := D.domain.defining b.val.val hfrontier
    let rho := R.rho ∘ (Subtype.val : D.domain.Point → D.domain.extension.Point)
    ∃ beta : Model (k + 1) → ℝ,
      rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
      (∀ᶠ y in 𝓝 b.val, rho y = 0 ↔ (𝓡∂ (k + 1)).IsBoundaryPoint y) ∧
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val ≠ 0 ∧
      ContDiffAt ℝ ∞ beta
        ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val) ∧
      beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val)]
        (rho ∘ ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).symm) ∧
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val
        (IntrinsicLiouville.liouvilleVector (D.domain.restrictForm D.liouville.primitive)
          (IntrinsicLiouville.exteriorDerivative
            (D.domain.restrictForm D.liouville.primitive)) b.val)) := by
  let hfrontier := (D.domain.isBoundaryPoint_iff_frontier b.val).mp b.property
  let R := D.domain.defining b.val.val hfrontier
  let rho := R.rho ∘ (Subtype.val : D.domain.Point → D.domain.extension.Point)
  let e := (IntrinsicBoundary.chartAt b).ambient
  have hbs : b.val ∈ e.source := by
    have hb := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at hb
  obtain ⟨beta, U, hU, hbU, hbeta, heq⟩ := D.domain.exists_scalar_restriction_germ
    R.rho R.neighbourhood R.open_neighbourhood R.smooth_rho e
      (IntrinsicBoundary.chartAt b).mem_atlas b.val hbs R.mem_neighbourhood
  have hR : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ R.rho b.val.val :=
    R.smooth_rho.contMDiffAt (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)
  have hchain := mfderiv_comp (f := (Subtype.val : D.domain.Point →
    D.domain.extension.Point)) (g := R.rho) b.val
      (hR.mdifferentiableAt (by simp))
      (D.domain.contMDiff_subtype_val.mdifferentiableAt (by simp))
  change ∃ beta : Model (k + 1) → ℝ, _
  refine ⟨beta, (R.zero_level b.val.val R.mem_neighbourhood).mp hfrontier,
    ?_, ?_, ?_, hbeta.contDiffAt (hU.mem_nhds hbU), heq, ?_⟩
  · filter_upwards [D.domain.contMDiff_subtype_val.continuous.continuousAt.preimage_mem_nhds
      (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)] with y hy
    exact (R.sublevel y.val hy).mp y.property
  · filter_upwards [D.domain.contMDiff_subtype_val.continuous.continuousAt.preimage_mem_nhds
      (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)] with y hy
    exact ((R.zero_level y.val hy).symm).trans
      (D.domain.isBoundaryPoint_iff_frontier y).symm
  · intro hz
    apply R.regular
    ext v
    obtain ⟨u, rfl⟩ := (D.nativePresentation.tangent_bijective b.val).2 v
    have h := congrArg (fun A => A u) hchain
    rw [hz] at h
    exact h.symm
  · rw [hchain]
    change 0 < (show ℝ from mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) R.rho b.val.val
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (Subtype.val : D.domain.Point → D.domain.extension.Point) b.val
        (IntrinsicLiouville.liouvilleVector (D.domain.restrictForm D.liouville.primitive)
          (IntrinsicLiouville.exteriorDerivative
            (D.domain.restrictForm D.liouville.primitive)) b.val)))
    rw [← D.native_field_inclusion]
    exact D.liouville.outward b.val.val hfrontier

/-- Cohesive native defining laws for the actual compact restriction.
Smoothness, closed symplectic differential and canonical contraction hold
on full tangent spaces; outwardness uses the stored defining functions. -/
theorem native_liouville_laws :
    let alpha := D.domain.restrictForm D.liouville.primitive
    IntrinsicLiouville.IsLocallyExtendibleForm alpha ∧
    IntrinsicLiouville.HasExteriorDerivative alpha (IntrinsicLiouville.exteriorDerivative alpha) ∧
    IntrinsicLiouville.IsLocallyExtendibleForm (IntrinsicLiouville.exteriorDerivative alpha) ∧
    IntrinsicLiouville.exteriorDerivative (IntrinsicLiouville.exteriorDerivative alpha) = 0 ∧
    (∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative alpha) x) ∧
    IntrinsicLiouville.Contraction alpha (IntrinsicLiouville.exteriorDerivative alpha)
      (IntrinsicLiouville.liouvilleVector alpha (IntrinsicLiouville.exteriorDerivative alpha)) ∧
    ∀ b : IntrinsicBoundary.Point k D.domain.Point,
      ∃ (rho : D.domain.Point → ℝ) (beta : Model (k + 1) → ℝ),
        rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
        (∀ᶠ y in 𝓝 b.val, rho y = 0 ↔ (𝓡∂ (k + 1)).IsBoundaryPoint y) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val
          (IntrinsicLiouville.liouvilleVector alpha
            (IntrinsicLiouville.exteriorDerivative alpha) b.val)) := by
  have halpha := D.domain.isLocallyExtendibleForm_restrictForm
    D.liouville.primitive D.liouville.smooth_primitive
  refine ⟨halpha, IntrinsicLiouville.hasExteriorDerivative_exteriorDerivative _ halpha,
    IntrinsicLiouville.isLocallyExtendibleForm_exteriorDerivative _ halpha,
    IntrinsicLiouville.exteriorDerivative_exteriorDerivative _ halpha,
    D.native_nondegenerate,
    IntrinsicLiouville.contraction_liouvilleVector _ _ D.native_nondegenerate, ?_⟩
  intro b
  exact ⟨_, D.native_definingFunction_laws b⟩

/-- The native canonical Liouville field has smooth real open coefficients
in every original native chart. Its regularity is proved from the restricted
primitive and nondegeneracy, including at boundary points. -/
theorem native_field_coordinate_germs
    (e : OpenPartialHomeomorph D.domain.Point (EuclideanHalfSpace (k + 1)))
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) D.domain.Point)
    (x : D.domain.Point) (hx : x ∈ e.source) :
    ∃ (f : Model (k + 1) → Model (k + 1)) (V : Set (Model (k + 1))),
      IsOpen V ∧ e.extend (𝓡∂ (k + 1)) x ∈ V ∧ ContDiffOn ℝ ∞ f V ∧
      f =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
        (e.extend (𝓡∂ (k + 1)) x)]
        IntrinsicLiouville.vectorInChart e
          (IntrinsicLiouville.liouvilleVector (D.domain.restrictForm D.liouville.primitive)
            (IntrinsicLiouville.exteriorDerivative
              (D.domain.restrictForm D.liouville.primitive))) := by
  have h := D.native_liouville_laws
  exact IntrinsicLiouville.exists_liouville_coefficients he _ _ h.1 h.2.1 h.2.2.2.2.1
    _ h.2.2.2.2.2.1 hx

end LiouvilleDomain

end FsFltz.Geometry
