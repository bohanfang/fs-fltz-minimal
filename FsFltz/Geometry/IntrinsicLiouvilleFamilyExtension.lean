import FsFltz.Geometry.IntrinsicExtensionSymplectic
import FsFltz.Geometry.IntrinsicExtensionOutward
import FsFltz.Geometry.IntrinsicNativePrimitiveFamily
import FsFltz.Geometry.CompactDomainRestrictionPresentation
import FsFltz.Geometry.FamilyLiouvilleNeighborhood
import FsFltz.Geometry.FamilyCompletionAssembly

/-!
# Native Liouville families on one symplectic extension

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 783–814.
One fixed native compact presentation and jointly smooth extended primitives
produce one common spatial symplectic neighborhood for the entire compact
parameter interval. The full native primitive and derivative determine the
actual Liouville fields and their outwardness. The existing localized
completion-family construction then supplies both the collars and the
completed primitive and field families.

This positive-dimensional foundation concerns a fixed native manifold. It
does not trivialize domain bundles, assemble witnessed pair families, or
assert any part of the geometric target `thm:target`, lines 352–415.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

namespace SmoothManifold

/-- Every required time slice of a jointly smooth interval form family is
smooth. No smoothness of the auxiliary real slices outside the interval is
asserted. -/
theorem isSmoothForm_of_isSmoothIntervalFormFamily {d q : ℕ}
    (N : SmoothManifold d) (lam : Parameter → N.Form q)
    (hlam : N.IsSmoothIntervalFormFamily lam) (t : Parameter) :
    N.IsSmoothForm (lam t) := by
  obtain ⟨eta, heta, he⟩ := hlam
  rw [← he t]
  intro a y hy
  obtain ⟨U, hU, hcover, hsm⟩ := heta a
  exact ((hsm.contDiffAt (hU.mem_nhds (hcover (show (t.val, y) ∈
    parameterInterval ×ˢ (chartAt (Model d) a).target from ⟨t.property, hy⟩)))).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

end SmoothManifold

namespace CompactDomain

/-- Joint smoothness and nondegeneracy on the compact interval times carrier
give a single spatial open symplectic neighborhood for every interval slice.
The tube lemma uses compactness of both factors; all geometric hypotheses
are restricted to the prescribed parameter interval. -/
theorem exists_common_symplecticNeighborhood_of_primitiveFamily {d : ℕ}
    (D : CompactDomain d) (lam : Parameter → D.extension.Form 1)
    (hlam : D.extension.IsSmoothIntervalFormFamily lam)
    (hnd : ∀ t x, x ∈ D.carrier →
      D.extension.Nondegenerate (D.extension.exteriorDerivative (lam t)) x) :
    ∃ U : TopologicalSpace.Opens D.extension.Point, D.carrier ⊆ U ∧
      ∀ t : Parameter, ∀ x ∈ U,
        D.extension.Nondegenerate (D.extension.exteriorDerivative (lam t)) x := by
  obtain ⟨eta, heta, he⟩ := hlam
  let S : Set (Set (ℝ × D.extension.Point)) := {V | IsOpen V ∧
    ∀ p ∈ V, D.extension.Nondegenerate (D.extension.exteriorDerivative (eta p.1)) p.2}
  have hV : IsOpen (⋃₀ S) := isOpen_sUnion (fun _ hs => hs.1)
  have hcover : parameterInterval ×ˢ D.carrier ⊆ ⋃₀ S := by
    intro p hp
    have hn : D.extension.Nondegenerate (D.extension.exteriorDerivative (eta p.1)) p.2 := by
      rw [he ⟨p.1, hp.1⟩]
      exact hnd ⟨p.1, hp.1⟩ p.2 hp.2
    obtain ⟨V, ho, hpV, hnV, _⟩ :=
      D.extension.exists_liouvilleVector_family_neighborhood_at eta heta p hp.1 hn
    exact mem_sUnion.mpr ⟨V, ⟨ho, hnV⟩, hpV⟩
  obtain ⟨J, U, _hJ, hU, htime, hcarrier, hprod⟩ :=
    generalized_tube_lemma isCompact_Icc D.compact hV hcover
  refine ⟨⟨U, hU⟩, hcarrier, ?_⟩
  intro t x hx
  obtain ⟨V, hVS, hpV⟩ := mem_sUnion.mp
    (hprod (show (t.val, x) ∈ J ×ˢ U from ⟨htime t.property, hx⟩))
  have hn := hVS.2 (t.val, x) hpV
  rwa [he t] at hn

end CompactDomain

namespace IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
/-- A single fixed native presentation carrying jointly smooth primitives
produces a Liouville family on one common symplectic spatial restriction.
Every primitive, derivative and actual field pullback holds on all native
tangent directions, including the boundary. The localized completion family
is constructed from this same varying family, without supplied completions.
-/
theorem exists_liouvilleFamily_of_native_primitiveFamily_and_coordinates
    (α : Parameter → Form k M 1)
    (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (he : ∀ x, (e x).val = i x)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hemb : Topology.IsClosedEmbedding i)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hrange : range i = D.carrier)
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (lam : Parameter → D.extension.Form 1)
    (hlam : D.extension.IsSmoothIntervalFormFamily lam)
    (hpull : ∀ t, (fun x => (lam t (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val))) :
    ∃ (D' : CompactDomain (k + 1)) (j : M → D'.extension.Point)
      (e' : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D'.Point ∞)
      (L : Parameter → LiouvilleStructure D'),
      (∀ x, (e' x).val = j x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j ∧
      Topology.IsClosedEmbedding j ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) ∧
      range j = D'.carrier ∧
      frontier D'.carrier = j '' (𝓡∂ (k + 1)).boundary M ∧
      D'.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      D'.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      (∀ t, (fun x => ((L t).primitive (j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = α t) ∧
      (∀ t, (fun x => (D'.extension.exteriorDerivative (L t).primitive (j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = exteriorDerivative (α t)) ∧
      (∀ t x, (L t).field (j x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x
          (liouvilleVector (α t) (exteriorDerivative (α t)) x)) ∧
      (∀ t, D'.extension.IsSymplecticOn
        (D'.extension.exteriorDerivative (L t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily D' L) ∧
      (HasNativeCoordinateExtensions (k := k) D.extension i →
        HasNativeCoordinateExtensions (k := k) D'.extension j) := by
  have hsm (t : Parameter) : D.extension.IsSmoothForm (lam t) :=
    D.extension.isSmoothForm_of_isSmoothIntervalFormFamily lam hlam t
  have hDnd : ∀ t x, x ∈ D.carrier →
      D.extension.Nondegenerate (D.extension.exteriorDerivative (lam t)) x := by
    intro t y hy
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact nondegenerate_exteriorDerivative_of_native_pullback D.extension i hi
      (lam t) (hsm t) (α t) (hpull t) x (hbij x) (hnd t x)
  obtain ⟨U, hU, hUnd⟩ := D.exists_common_symplecticNeighborhood_of_primitiveFamily lam hlam hDnd
  let D' := D.restrict U hU
  let := D'.halfSpaceChartedSpace
  let e' : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D'.Point ∞ :=
    e.trans (D.restrictPointDiffeomorph U hU).symm
  let j : M → D'.extension.Point := fun x => (e' x).val
  have hjval (x : M) : (j x).val = i x := by
    change (e x).val = i x
    exact he x
  have hval : (Subtype.val : D'.extension.Point → D.extension.Point) ∘ j = i :=
    funext hjval
  have hj : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j :=
    D'.contMDiff_subtype_val.comp e'.contMDiff
  have hjemb : Topology.IsClosedEmbedding j :=
    Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal (hval ▸ hemb)
  have hdj (x : M) : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x := by
    have hd := mfderiv_comp (f := j)
      (g := (Subtype.val : D'.extension.Point → D.extension.Point)) x
      ((D.extension.restrictInclusion U).map.contMDiff.mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))
    rw [hval] at hd
    erw [D.extension.mfderiv_restrict_val U (j x)] at hd
    exact hd.symm
  have hjbij (x : M) : Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x) := by
    rw [hdj]
    exact hbij x
  have hjrange : range j = D'.carrier := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change (j x).val ∈ D.carrier
      rw [hjval, ← hrange]
      exact mem_range_self x
    · intro hy
      change y.val ∈ D.carrier at hy
      rw [← hrange] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext ((hjval x).trans hx)⟩
  have hjfrontier : frontier D'.carrier = j '' (𝓡∂ (k + 1)).boundary M := by
    rw [D.frontier_restrict_carrier U, hfrontier]
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext ((hjval x).trans hxy)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hjval x).symm⟩
  let lam' : Parameter → D'.extension.Form 1 :=
    fun t => D'.extension.pullback D.extension Subtype.val (lam t)
  have hsm' (t : Parameter) : D'.extension.IsSmoothForm (lam' t) :=
    D'.extension.isSmoothForm_pullback_one D.extension
      (D.extension.restrictInclusion U).map (lam t) (hsm t)
  have hnd' (t : Parameter) (x : D'.extension.Point) :
      D'.extension.Nondegenerate (D'.extension.exteriorDerivative (lam' t)) x := by
    intro v hv
    apply hUnd t x.val x.property v
    intro w
    have heq := hv w
    unfold SmoothManifold.evalTwo at heq ⊢
    rw [D.extension.exteriorDerivative_restrict U (lam t) (hsm t) x] at heq
    exact heq
  have hglobal (t : Parameter) : D'.extension.IsSymplecticOn
      (D'.extension.exteriorDerivative (lam' t)) univ :=
    (D'.extension.isSymplecticOn_exteriorDerivative_iff _ (hsm' t) _).mpr
      (fun x _ => hnd' t x)
  have hpull' (t : Parameter) : (fun x => (lam' t (j x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = α t := by
    funext x
    dsimp only [lam']
    rw [D.extension.pullback_restrict_val U (lam t) (j x), hjval, hdj]
    exact congrFun (hpull t) x
  have hderiv' (t : Parameter) : (fun x =>
      (D'.extension.exteriorDerivative (lam' t) (j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = exteriorDerivative (α t) := by
    have hd := exteriorDerivative_pullback_from_boundaryless D'.extension j hj (lam' t) (hsm' t)
    rw [hpull' t] at hd
    exact hd.symm
  let F := fun t : Parameter => D'.extension.liouvilleVector (lam' t)
  have hfield' (t : Parameter) (x : M) : F t (j x) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x
        (liouvilleVector (α t) (exteriorDerivative (α t)) x) :=
    liouvilleVector_extension_eq D'.extension j (α t) (lam' t) (hnd t)
      (congrFun (hpull' t)) (congrFun (hderiv' t)) x (hjbij x).2 (hnd' t (j x))
  have hnegative (t : Parameter) (b : IntrinsicBoundary.Point k M) :
      (show Model (k + 1) from chartTangentMap (IntrinsicBoundary.chartAt b).ambient
        b.val (liouvilleVector (α t) (exteriorDerivative (α t)) b.val)) 0 < 0 := by
    obtain ⟨rho, beta, hz, hs, hr, hb, hag, hpos⟩ := hout t b
    have hesource : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source b
      rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
    exact (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt b).mem_atlas hesource b.property rho hz hs hr hb hag
      (liouvilleVector (α t) (exteriorDerivative (α t)) b.val)).mp hpos
  let L : Parameter → LiouvilleStructure D' := fun t =>
    { primitive := lam' t
      smooth_primitive := hsm' t
      symplectic := ⟨(hglobal t).1, fun x _ => (hglobal t).2.1 x (mem_univ x),
        fun x _ => (hglobal t).2.2 x (mem_univ x)⟩
      field := F t
      smooth_field := D'.extension.isSmoothVectorField_liouvilleVector _ (hsm' t) (hnd' t)
      contraction := fun x _ => D'.extension.liouvilleVector_contraction _ x
        (D'.extension.liouvilleEquation_exists _ x (hnd' t x))
      outward := outward_compactDomain_extension D' j hj (fun x => (hjbij x).2)
        hjrange hjfrontier (liouvilleVector (α t) (exteriorDerivative (α t)))
          (F t) (hfield' t) (hnegative t) }
  have hL : D'.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) :=
    D'.extension.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family D.extension
      (fun _ x => x.val) (contMDiff_subtype_val.comp contMDiff_snd) lam hlam
  have hF : D'.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) :=
    D'.extension.isSmoothIntervalVectorFieldFamily_liouvilleVector lam' hL hnd'
  refine ⟨D', j, e', L, fun _ => rfl, hj, hjemb, hjbij, hjrange, hjfrontier,
    hL, hF, hpull', hderiv', hfield', hglobal, ⟨D'.localizedCompletionFamily L hL⟩, ?_⟩
  intro hcoord x
  obtain ⟨a, O, Q, ha, hO, hxO, hQ, heq⟩ := hcoord x
  refine ⟨a, Subtype.val ⁻¹' O, Q ∘ Subtype.val, ha,
    hO.preimage continuous_subtype_val, ?_,
    hQ.comp contMDiff_subtype_val.contMDiffOn (fun _ hz => hz), ?_⟩
  · change (j x).val ∈ O
    rw [hjval]
    exact hxO
  · intro y hy
    change (j y).val ∈ O at hy
    rw [hjval] at hy
    obtain ⟨hsource, hagree⟩ := heq y hy
    exact ⟨hsource, by change Q (j y).val = _; rw [hjval]; exact hagree⟩

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
/-- Forgetting transported source coordinates preserves the original
Liouville-family API and its completed-family conclusion. -/
theorem exists_liouvilleFamily_of_native_primitiveFamily
    (α : Parameter → Form k M 1)
    (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
    (he : ∀ x, (e x).val = i x)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hemb : Topology.IsClosedEmbedding i)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hrange : range i = D.carrier)
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (lam : Parameter → D.extension.Form 1)
    (hlam : D.extension.IsSmoothIntervalFormFamily lam)
    (hpull : ∀ t, (fun x => (lam t (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val))) :
    ∃ (D' : CompactDomain (k + 1)) (j : M → D'.extension.Point)
      (e' : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D'.Point ∞)
      (L : Parameter → LiouvilleStructure D'),
      (∀ x, (e' x).val = j x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j ∧
      Topology.IsClosedEmbedding j ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) ∧
      range j = D'.carrier ∧
      frontier D'.carrier = j '' (𝓡∂ (k + 1)).boundary M ∧
      D'.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      D'.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      (∀ t, (fun x => ((L t).primitive (j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = α t) ∧
      (∀ t, (fun x => (D'.extension.exteriorDerivative (L t).primitive (j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = exteriorDerivative (α t)) ∧
      (∀ t x, (L t).field (j x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x
          (liouvilleVector (α t) (exteriorDerivative (α t)) x)) ∧
      (∀ t, D'.extension.IsSymplecticOn
        (D'.extension.exteriorDerivative (L t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily D' L) := by
  obtain ⟨D', j, e', L, he', hj, hjemb, hjbij, hjrange, hjfrontier,
    hL, hF, hpull', hderiv', hfield', hglobal, hcompletion, _⟩ :=
    exists_liouvilleFamily_of_native_primitiveFamily_and_coordinates
      α D i e he hi hemb hbij hrange hfrontier lam hlam hpull hnd hout
  exact ⟨D', j, e', L, he', hj, hjemb, hjbij, hjrange, hjfrontier,
    hL, hF, hpull', hderiv', hfield', hglobal, hcompletion⟩

/-- Original jointly extendible native primitives, with nondegeneracy and
local defining-function outwardness at every required parameter, construct
one fixed native Liouville presentation and its localized completion family.
The reference slice constructs the underlying collar presentation; the whole
primitive family is extended on that presentation before one common spatial
symplectic restriction is chosen. Neither extended forms, collars, completed
ambients, nor field-preservation certificates are supplied as hypotheses.
-/
theorem exists_liouvilleFamily_with_native_presentation_and_coordinates
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
      (L : Parameter → LiouvilleStructure D),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      (∀ t, (fun x => ((L t).primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t) ∧
      (∀ t, (fun x => (D.extension.exteriorDerivative (L t).primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = exteriorDerivative (α t)) ∧
      (∀ t x, (L t).field (i x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
          (liouvilleVector (α t) (exteriorDerivative (α t)) x)) ∧
      (∀ t, D.extension.IsSymplecticOn
        (D.extension.exteriorDerivative (L t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily D L) ∧ HasNativeCoordinateExtensions (k := k) D.extension i := by
  obtain ⟨D, i, e, lam, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hcoord⟩ :=
    exists_compactDomain_with_native_primitiveFamily_and_coordinates α hα
      (hnd parameterZero) (hout parameterZero)
  obtain ⟨D', j, e', L, he', hj, hjemb, hjbij, hjrange, hjfrontier,
    hL, hF, hpull', hderiv', hfield', hglobal, hcompletion, htransport⟩ :=
    exists_liouvilleFamily_of_native_primitiveFamily_and_coordinates α D i e he hi hemb hbij
      hrange hfrontier lam hlam hpull hnd hout
  exact ⟨D', j, e', L, he', hj, hjemb, hjbij, hjrange, hjfrontier,
    hL, hF, hpull', hderiv', hfield', hglobal, hcompletion, htransport hcoord⟩

/-- The original native family API is the projection of the stronger
producer that also retains actual source-coordinate extension germs. -/
theorem exists_liouvilleFamily_with_native_presentation
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
      (L : Parameter → LiouvilleStructure D),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      (∀ t, (fun x => ((L t).primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t) ∧
      (∀ t, (fun x => (D.extension.exteriorDerivative (L t).primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = exteriorDerivative (α t)) ∧
      (∀ t x, (L t).field (i x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
          (liouvilleVector (α t) (exteriorDerivative (α t)) x)) ∧
      (∀ t, D.extension.IsSymplecticOn
        (D.extension.exteriorDerivative (L t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily D L) := by
  obtain ⟨D, i, e, L, he, hi, hemb, hbij, hrange, hfrontier,
    hL, hF, hpull, hderiv, hfield, hglobal, hcompletion, _⟩ :=
    exists_liouvilleFamily_with_native_presentation_and_coordinates α hα hnd hout
  exact ⟨D, i, e, L, he, hi, hemb, hbij, hrange, hfrontier,
    hL, hF, hpull, hderiv, hfield, hglobal, hcompletion⟩

end IntrinsicLiouville
end FsFltz.Geometry
