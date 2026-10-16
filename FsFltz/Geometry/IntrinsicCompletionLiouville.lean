import FsFltz.Geometry.IntrinsicCompletionDomain
import FsFltz.Geometry.IntrinsicCompletionPrimitive
import FsFltz.Geometry.IntrinsicExtensionLiouville
import FsFltz.Geometry.IntrinsicExtensionOutward
import FsFltz.Geometry.SmoothLiouville

/-!
# The Liouville domain on the original intrinsic completion quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The single primitive produced on the actual half-infinite
quotient determines a smooth canonical Liouville field. Full native
primitive pullback determines its field at every original point, including
the boundary seam. The original native outwardness then proves outwardness
for the actual compact domain's defining functions. Neither a target field
nor target outwardness, complete flow, or completion is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing
open SmoothManifold

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

/-- The actual quotient compact domain has precisely the native boundary
image as its frontier; the identity uses its produced boundary inclusion. -/
theorem compactDomain_frontier [CompactSpace M] :
    frontier (compactDomain hδ C hemb hC hboundary hinv hzero).carrier =
      original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) ''
        (𝓡∂ (k + 1)).boundary M := by
  rw [← (compactDomain hδ C hemb hC hboundary hinv hzero).boundary_range]
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, b.property, (compactDomain_boundaryInclusion hδ C hemb hC hboundary hinv hzero b).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, compactDomain_boundaryInclusion hδ C hemb hC hboundary hinv hzero ⟨m, hm⟩⟩

/-- Full native primitive preservation forces the canonical field of the
same quotient primitive to be the actual differential image of the native
Liouville field, including at every original boundary point. -/
theorem liouvilleVector_original
    (α : IntrinsicLiouville.Form k M 1)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (lam : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hlam : (completionManifold hδ C hemb hC hboundary hinv hzero).IsSmoothForm lam)
    (hnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      (fun x => (lam (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x)) = α)
    (hglobal : ∀ x, (completionManifold hδ C hemb hC hboundary hinv hzero).Nondegenerate
      ((completionManifold hδ C hemb hC hboundary hinv hzero).exteriorDerivative lam) x)
    (x : M) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    (completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleVector lam
      (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x
            (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x) := by
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  let := completionChartedSpace hδ C hemb hboundary hzero
  have hd := IntrinsicLiouville.exteriorDerivative_pullback_from_boundaryless X (original c)
    (contMDiff_original hδ C hemb hC hboundary hinv hzero) lam hlam
  rw [hnative] at hd
  exact IntrinsicLiouville.liouvilleVector_extension_eq X (original c) α lam hnd
    (congrFun hnative) (congrFun hd.symm) x
    (bijective_mfderiv_original hδ C hemb hC hboundary hinv hzero x).2 (hglobal _)

variable [CompactSpace M]

/-- The actual globally smooth primitive gives a Liouville structure on
this very quotient compact domain. Outwardness is derived from the original
native field's negative normal coefficient, not supplied on the quotient. -/
def liouvilleStructure
    (α : IntrinsicLiouville.Form k M 1)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (lam : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hlam : (completionManifold hδ C hemb hC hboundary hinv hzero).IsSmoothForm lam)
    (hnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      (fun x => (lam (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x)) = α)
    (hglobal : ∀ x, (completionManifold hδ C hemb hC hboundary hinv hzero).Nondegenerate
      ((completionManifold hδ C hemb hC hboundary hinv hzero).exteriorDerivative lam) x)
    (hnegative : ∀ b : IntrinsicBoundary.Point k M,
      (show Model (k + 1) from IntrinsicLiouville.chartTangentMap (IntrinsicBoundary.chartAt b).ambient
        b.val (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) b.val)) 0 < 0) :
    LiouvilleStructure (compactDomain hδ C hemb hC hboundary hinv hzero) := by
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  let D := compactDomain hδ C hemb hC hboundary hinv hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  exact
    { primitive := lam
      smooth_primitive := hlam
      symplectic := (X.isSymplecticOn_exteriorDerivative_iff lam hlam D.carrier).mpr
        (fun x _ => hglobal x)
      field := X.liouvilleVector lam
      smooth_field := X.isSmoothVectorField_liouvilleVector lam hlam hglobal
      contraction := fun x _ => X.liouvilleVector_contraction lam x
        (X.liouvilleEquation_exists lam x (hglobal x))
      outward := IntrinsicLiouville.outward_compactDomain_extension D (original c)
        (contMDiff_original hδ C hemb hC hboundary hinv hzero)
        (fun x => (bijective_mfderiv_original hδ C hemb hC hboundary hinv hzero x).2)
        (compactDomain_carrier hδ C hemb hC hboundary hinv hzero).symm
        (compactDomain_frontier hδ C hemb hC hboundary hinv hzero)
        (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α))
        (X.liouvilleVector lam)
        (liouvilleVector_original hδ C hemb hC hboundary hinv hzero α hnd lam hlam hnative hglobal)
        hnegative }

/-- Construct a Liouville structure using the one primitive produced on
this exact quotient. Its finite, whole-cylinder and all-native-tangent
primitive laws and global nondegeneracy all refer to that same structure. -/
theorem exists_liouvilleStructure
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y))
      (fun x => -IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x) (Ico 0 δ))
    (hnegative : ∀ b : IntrinsicBoundary.Point k M,
      (show Model (k + 1) from IntrinsicLiouville.chartTangentMap (IntrinsicBoundary.chartAt b).ambient
        b.val (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) b.val)) 0 < 0) :
    let X := completionManifold hδ C hemb hC hboundary hinv hzero
    let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
    let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ∃ L : LiouvilleStructure (compactDomain hδ C hemb hC hboundary hinv hzero),
      N.pullback X (finiteIn c) L.primitive =
        IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α ∧
      (fun x => (L.primitive (original c x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x)) = α ∧
      P.pullback X (cylinder c) L.primitive = cylinderPrimitive δ α ∧
      (∀ x, X.Nondegenerate (X.exteriorDerivative L.primitive) x) ∧
      L.field = X.liouvilleVector L.primitive ∧
      (∀ x, L.field (original c x) = mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x
        (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x)) := by
  obtain ⟨lam, hlam, hfinite, hnative, hcylinder, hglobal⟩ :=
    exists_smooth_symplectic_primitive hδ C hemb hC hboundary hinv hzero α hα hnd
      (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α))
      (IntrinsicLiouville.contraction_liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) hnd) hode
  let L := liouvilleStructure hδ C hemb hC hboundary hinv hzero α hnd lam hlam hnative hglobal hnegative
  refine ⟨L, hfinite, hnative, hcylinder, hglobal, rfl, ?_⟩
  exact liouvilleVector_original hδ C hemb hC hboundary hinv hzero α hnd lam hlam hnative hglobal

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicLiouville
open IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original native primitive data alone construct one collar, its actual
full quotient compact domain, and a Liouville structure on that domain.
Every displayed primitive and field equation concerns the same quotient
and the same selected primitive. No collar or target outwardness is input. -/
theorem exists_liouvilleStructure_from_native
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (C : ℝ × IntrinsicBoundary.Point k M → M) (δ : ℝ) (hδ : 0 < δ)
      (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
      (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Half δ (IntrinsicBoundary.Point k M)))
      (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
        (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
      (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
        ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
          ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
            ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
      (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val),
      let X := completionManifold hδ C hemb hC hboundary hinv hzero
      let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
      let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
      let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
      letI := completionChartedSpace hδ C hemb hboundary hzero
      ∃ L : LiouvilleStructure (compactDomain hδ C hemb hC hboundary hinv hzero),
        N.pullback X (finiteIn c) L.primitive =
          IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α ∧
        (fun x => (L.primitive (original c x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x)) = α ∧
        P.pullback X (cylinder c) L.primitive = cylinderPrimitive δ α ∧
        (∀ x, X.Nondegenerate (X.exteriorDerivative L.primitive) x) ∧
        L.field = X.liouvilleVector L.primitive ∧
        (∀ x, L.field (original c x) = mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x
          (liouvilleVector α (exteriorDerivative α) x)) ∧
        (∀ y, IsMIntegralCurveOn (fun t => C (t, y))
          (fun x => -liouvilleVector α (exteriorDerivative α) x) (Ico 0 δ)) := by
  obtain ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, _, _⟩ :=
    exists_topological_extension_with_primitive_collar α hα hnd hout
  have hb : ∀ p : Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0 :=
    fun p => hboundary p.val.2 p.val.1 p.property.1
  have hnegative (b : IntrinsicBoundary.Point k M) :
      (show Model (k + 1) from chartTangentMap (IntrinsicBoundary.chartAt b).ambient
        b.val (liouvilleVector α (exteriorDerivative α) b.val)) 0 < 0 := by
    obtain ⟨rho, beta, hz, hs, hr, hbeta, hag, hpos⟩ := hout b
    have hsource : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source b
      rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
    exact (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt b).mem_atlas hsource b.property rho hz hs hr hbeta hag
      (liouvilleVector α (exteriorDerivative α) b.val)).mp hpos
  obtain ⟨L, hfinite, hnative, hcylinder, hglobal, hfield, hfieldNative⟩ :=
    exists_liouvilleStructure hδ C hemb hC hb hinv hzero α hα hnd hode hnegative
  exact ⟨C, δ, hδ, hemb, hC, hb, hinv, hzero,
    L, hfinite, hnative, hcylinder, hglobal, hfield, hfieldNative, hode⟩

end FsFltz.Geometry.IntrinsicLiouville
