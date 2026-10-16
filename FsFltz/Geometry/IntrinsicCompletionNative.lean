import FsFltz.Geometry.IntrinsicCompletionLiouville
import FsFltz.Geometry.IntrinsicCompletion
import FsFltz.Geometry.IntrinsicCollarPresentation
import FsFltz.Geometry.IntrinsicNativeEndpointPresentation

/-!
# The native presentation on the actual intrinsic completion quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–160, and `sec:lean`,
lines 805–814. The original native manifold is diffeomorphic to the literal
compact carrier in the constructed half-infinite quotient. The same finite
patch transports its native coordinate extensions into this full quotient.
The resulting native Liouville presentation retains the actual quotient,
its selected primitive, and every original point.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- Native coordinate extensions transport through a smooth embedding of
equal ambient dimension. A smooth inverse on an actual open neighborhood
is constructed by the inverse function theorem at each native point. -/
theorem HasNativeCoordinateExtensions.of_smoothEmbedding_square {d : ℕ}
    (N P : SmoothManifold d) (i : M → N.Point) (j : M → P.Point)
    (hi : HasNativeCoordinateExtensions (k := k) N i)
    (f : N.SmoothEmbedding P) (hsquare : ∀ x, f.map (i x) = j x) :
    HasNativeCoordinateExtensions (k := k) P j := by
  intro x
  obtain ⟨a, O, Q, ha, hO, hx, hQ, hag⟩ := hi x
  let hlocal := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ f.map.contMDiff.contMDiffOn (mem_univ (i x))
    (show Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.map (i x)) from
      ⟨f.immersion _, LinearMap.injective_iff_surjective.mp (f.immersion _)⟩)
  let g := hlocal.localInverse
  let U : Set P.Point := g.source ∩ g ⁻¹' O
  have hU : IsOpen U := g.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    g.open_source hO
  have hgx : g (j x) = i x := by
    rw [← hsquare x]
    exact hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  refine ⟨a, U, Q ∘ g, ha, hU, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [← hsquare x]
      exact hlocal.localInverse_mem_source
    · change g (j x) ∈ O
      rw [hgx]
      exact hx
  · exact hQ.comp (g.contMDiffOn_toFun.mono inter_subset_left) (fun _ hz => hz.2)
  · intro y hy
    have hgy : g (j y) = i y :=
      f.embedding.injective ((hlocal.localInverse_right_inv hy.1).trans (hsquare y).symm)
    have hyO : i y ∈ O := by
      have h := hy.2
      change g (j y) ∈ O at h
      rwa [hgy] at h
    exact ⟨(hag y hyO).1, by simpa only [Function.comp_apply, hgy] using (hag y hyO).2⟩

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M]
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

/-- The original quotient inclusion is a homeomorphism onto this actual
compact carrier, using its literal proved carrier equality. -/
def originalHomeomorph : M ≃ₜ (compactDomain hδ C hemb hC hboundary hinv hzero).Point :=
  (isClosedEmbedding_original hδ
    (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) hemb).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (compactDomain_carrier hδ C hemb hC hboundary hinv hzero).symm)

@[simp] theorem originalHomeomorph_val (x : M) :
    (originalHomeomorph hδ C hemb hC hboundary hinv hzero x).val =
      original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x := rfl

@[simp] theorem original_originalHomeomorph_symm
    (x : (compactDomain hδ C hemb hC hboundary hinv hzero).Point) :
    original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
      ((originalHomeomorph hδ C hemb hC hboundary hinv hzero).symm x) = x.val := by
  exact congrArg Subtype.val
    ((originalHomeomorph hδ C hemb hC hboundary hinv hzero).apply_symm_apply x)

/-- The original inclusion is smooth in the actual carrier's native atlas. -/
theorem contMDiff_originalHomeomorph :
    ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞
      (originalHomeomorph hδ C hemb hC hboundary hinv hzero) := by
  apply (compactDomain hδ C hemb hC hboundary hinv hzero).contMDiff_iff_subtype_val.mpr
  exact contMDiff_original hδ C hemb hC hboundary hinv hzero

/-- The carrier inverse is smooth: the finite-patch inverse germ restricts
to its actual compact carrier and the produced finite native diffeomorphism
then returns the original manifold. All fallback points come from the point
currently being checked, so empty carriers remain allowed. -/
theorem contMDiff_originalHomeomorph_symm :
    ContMDiff (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞
      (originalHomeomorph hδ C hemb hC hboundary hinv hzero).symm := by
  classical
  let D := compactDomain hδ C hemb hC hboundary hinv hzero
  let A := IntrinsicCollarGluing.compactDomain hδ C hemb hC hboundary hinv hzero
  let e := originalHomeomorph hδ C hemb hC hboundary hinv hzero
  let a := IntrinsicCollarGluing.originalDiffeomorph hδ C hemb hC hboundary hinv hzero
  let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  let := IntrinsicCollarGluing.extensionChartedSpace hδ C hemb hboundary hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  intro x
  let u : A.Point := a (e.symm x)
  have hux : finiteIn c u.val = x.val := original_originalHomeomorph_symm hδ C hemb hC hboundary hinv hzero x
  obtain ⟨g, hg, _, heq⟩ := finiteIn_inverse_germ hδ C hemb hC hboundary hinv hzero u.val
  rw [hux] at hg heq
  let b : D.Point → A.Point := fun y =>
    if hy : g y.val ∈ A.carrier then ⟨g y.val, hy⟩ else u
  have hn : ∀ᶠ y : D.Point in 𝓝 x, finiteIn c (g y.val) = y.val :=
    continuous_subtype_val.continuousAt.eventually heq
  have hb (y : D.Point) (hy : finiteIn c (g y.val) = y.val) :
      (b y).val = g y.val := by
    have hm : g y.val ∈ A.carrier := by
      have hcarrier : y.val ∈ finiteIn c '' A.carrier := y.property
      obtain ⟨z, hz, hzy⟩ := hcarrier
      have hgz : g y.val = z := finiteIn_injective c (hy.trans hzy.symm)
      rwa [hgz]
    simp [b, hm]
  have hbs : ContMDiffAt (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ∞ b x := by
    apply A.contMDiffAt_iff_subtype_val.mpr
    apply (hg.comp x D.contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    exact hb y hy
  apply (a.symm.contMDiffAt.comp x hbs).congr_of_eventuallyEq
  filter_upwards [hn] with y hy
  have hby : b y = a (e.symm y) := by
    apply Subtype.ext
    apply finiteIn_injective c
    rw [hb y hy, hy]
    exact (original_originalHomeomorph_symm hδ C hemb hC hboundary hinv hzero y).symm
  change e.symm y = a.symm (b y)
  rw [hby]
  exact (a.symm_apply_apply (e.symm y)).symm

/-- Native correspondence for the same compact domain in the full quotient. -/
def originalDiffeomorph : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1))
    M (compactDomain hδ C hemb hC hboundary hinv hzero).Point ∞ where
  toEquiv := (originalHomeomorph hδ C hemb hC hboundary hinv hzero).toEquiv
  contMDiff_toFun := contMDiff_originalHomeomorph hδ C hemb hC hboundary hinv hzero
  contMDiff_invFun := contMDiff_originalHomeomorph_symm hδ C hemb hC hboundary hinv hzero

@[simp] theorem originalDiffeomorph_val (x : M) :
    (originalDiffeomorph hδ C hemb hC hboundary hinv hzero x).val =
      original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x := rfl

omit [CompactSpace M] in
/-- The original source-coordinate extensions of the finite native collar
extend on the actual full quotient through its same finite patch. -/
theorem hasNativeCoordinateExtensions
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : ∀ b : IntrinsicBoundary.Point k M,
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (IntrinsicLiouville.normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
          (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) b.val)))
    (hode : ∀ b, IsMIntegralCurveOn (fun t => C (t, b))
      (fun z => -IntrinsicLiouville.liouvilleVector α
        (IntrinsicLiouville.exteriorDerivative α) z) (Ico 0 δ)) :
    IntrinsicLiouville.HasNativeCoordinateExtensions (k := k)
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) := by
  let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  have hfinite : IntrinsicLiouville.HasNativeCoordinateExtensions (k := k) N
      (IntrinsicCollarGluing.original c) := by
    intro x
    rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · let u : IntrinsicInterior.Point k M := ⟨x, hx⟩
      obtain ⟨O, Q, hO, hxO, hQ, hag⟩ :=
        IntrinsicCollarGluing.exists_interior_coordinate_extension hδ C hemb hC hboundary hinv hzero u
      exact ⟨chartAt (EuclideanHalfSpace (k + 1)) x, O, Q,
        chart_mem_atlas _ x, hO, hxO, hQ, hag⟩
    · let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
      obtain ⟨O, Q, hO, hxO, hQ, hag⟩ :=
        IntrinsicCollarGluing.exists_boundary_coordinate_extension_of_primitive
          hδ C hemb hC hboundary hinv hzero α hα hnd b (hout b) hode
      exact ⟨(IntrinsicBoundary.chartAt b).ambient, O, Q,
        (IntrinsicBoundary.chartAt b).mem_atlas, hO, hxO, hQ, hag⟩
  exact IntrinsicLiouville.HasNativeCoordinateExtensions.of_smoothEmbedding_square
    N X (IntrinsicCollarGluing.original c) (original c) hfinite
    (finitePatchEmbedding hδ C hemb hC hboundary hinv hzero) (fun _ => rfl)

/-- Package the actual quotient Liouville structure with its produced
native diffeomorphism and native coordinate extensions. The prescribed
structure and its primitive are retained literally. -/
def nativeLiouvillePresentation
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : ∀ b : IntrinsicBoundary.Point k M,
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (IntrinsicLiouville.normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
          (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) b.val)))
    (hode : ∀ b, IsMIntegralCurveOn (fun t => C (t, b))
      (fun z => -IntrinsicLiouville.liouvilleVector α
        (IntrinsicLiouville.exteriorDerivative α) z) (Ico 0 δ))
    (L : LiouvilleStructure (compactDomain hδ C hemb hC hboundary hinv hzero))
    (hnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      (fun x => (L.primitive (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) x)) = α) :
    IntrinsicLiouville.NativeLiouvillePresentation α :=
  IntrinsicLiouville.NativeLiouvillePresentation.of_endpoint α
    ⟨compactDomain hδ C hemb hC hboundary hinv hzero, L⟩
    (originalDiffeomorph hδ C hemb hC hboundary hinv hzero)
    (congrFun hnative)
    (hasNativeCoordinateExtensions hδ C hemb hC hboundary hinv hzero α hα hnd hout hode)

@[simp] theorem nativeLiouvillePresentation_domain
    (α : IntrinsicLiouville.Form k M 1) (hα hnd hout hode L hnative) :
    (nativeLiouvillePresentation hδ C hemb hC hboundary hinv hzero α hα hnd hout hode L hnative).domain =
      ⟨compactDomain hδ C hemb hC hboundary hinv hzero, L⟩ := rfl

@[simp] theorem nativeLiouvillePresentation_inclusion
    (α : IntrinsicLiouville.Form k M 1) (hα hnd hout hode L hnative) (x : M) :
    (nativeLiouvillePresentation hδ C hemb hC hboundary hinv hzero α hα hnd hout hode L hnative).inclusion x =
      original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x := rfl

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicLiouville
open IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original native primitive data produce a native presentation on the
same actual half-infinite quotient and the same Liouville structure.
The full cylinder primitive and its global nondegeneracy are retained for
the completion constructor on this precise domain. No ambient presentation,
native coordinate extensions or complete flow are inputs. -/
theorem exists_nativeLiouvillePresentation_on_quotient
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
      let B := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
      let c := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
      letI := completionChartedSpace hδ C hemb hboundary hzero
      ∃ (L : LiouvilleStructure (compactDomain hδ C hemb hC hboundary hinv hzero))
        (P : NativeLiouvillePresentation α),
        P.domain = ⟨compactDomain hδ C hemb hC hboundary hinv hzero, L⟩ ∧
        (∀ x, HEq (P.inclusion x) (original c x)) ∧
        N.pullback X (finiteIn c) L.primitive =
          IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α ∧
        (fun x => (L.primitive (original c x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x)) = α ∧
        B.pullback X (cylinder c) L.primitive = cylinderPrimitive δ α ∧
        (∀ x, X.Nondegenerate (X.exteriorDerivative L.primitive) x) ∧
        L.field = X.liouvilleVector L.primitive ∧
        (∀ x, L.field (original c x) = mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x
          (liouvilleVector α (exteriorDerivative α) x)) := by
  obtain ⟨C, δ, hδ, hemb, hC, hb, hinv, hzero, L,
    hfinite, hnative, hcylinder, hglobal, hfield, hfieldNative, hode⟩ :=
    exists_liouvilleStructure_from_native α hα hnd hout
  have hnormal (b : IntrinsicBoundary.Point k M) :
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
          (liouvilleVector α (exteriorDerivative α) b.val)) := by
    obtain ⟨rho, beta, hz, hs, hr, hbeta, hag, hpos⟩ := hout b
    have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source b
      rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
    have hn := (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt b).mem_atlas hx b.property rho hz hs hr hbeta hag
      (liouvilleVector α (exteriorDerivative α) b.val)).mp hpos
    rw [normalDefiningFunction_derivative (IntrinsicBoundary.chartAt b).mem_atlas hx]
    exact neg_pos.mpr hn
  let P := nativeLiouvillePresentation hδ C hemb hC hb hinv hzero α hα hnd hnormal hode L hnative
  exact ⟨C, δ, hδ, hemb, hC, hb, hinv, hzero, L, P,
    rfl, (fun _ => HEq.rfl), hfinite, hnative, hcylinder, hglobal, hfield, hfieldNative⟩

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] in
private theorem completion_native_primitive
    {α : Form k M 1} (P : NativeLiouvillePresentation α) (K : Completion P.domain) :
    (fun x => (K.ambient.primitive (K.inclusion.map (P.inclusion x))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (K.inclusion.map ∘ P.inclusion) x)) = α := by
  funext x
  rw [mfderiv_comp x (K.inclusion.map.contMDiff.mdifferentiableAt (by simp))
    (P.smooth_inclusion.mdifferentiableAt (by simp))]
  change (P.domain.domain.extension.pullback K.ambient.manifold K.inclusion.map
    K.ambient.primitive (P.inclusion x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion x) = α x
  rw [K.primitive_on_domain _ (P.carrier_range ▸ mem_range_self x)]
  exact congrFun P.primitive x

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] in
private theorem exists_completion_on_equal_native_domain
    {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (D : LiouvilleDomain (k + 1)) (hD : P.domain = D) (K : Completion D)
    (hambient : K.ambient.manifold = D.domain.extension)
    (hprimitive : HEq K.ambient.primitive D.liouville.primitive)
    (hinclusion : ∀ z : D.domain.extension.Point, HEq (K.inclusion.map z) z) :
    ∃ K' : Completion P.domain,
      K'.ambient.manifold = P.domain.domain.extension ∧
      HEq K'.ambient.primitive P.domain.liouville.primitive ∧
      (∀ z : P.domain.domain.extension.Point, HEq (K'.inclusion.map z) z) := by
  subst D
  exact ⟨K, hambient, hprimitive, hinclusion⟩

/-- Source-only native completion on the same produced quotient. The
ambient smooth manifold, primitive and full extension inclusion are retained
exactly, and the completed native marking preserves the original one-form
on every tangent direction. The construction uses the already selected
quotient and Liouville structure once; no second collar or primitive is chosen.
Source: `def:pair`, lines 142–160, and `sec:lean`, lines 805–814. -/
theorem exists_nativeLiouvillePresentation_with_completion
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
    ∃ (P : NativeLiouvillePresentation α) (K : Completion P.domain),
      K.ambient.manifold = P.domain.domain.extension ∧
      HEq K.ambient.primitive P.domain.liouville.primitive ∧
      (∀ z : P.domain.domain.extension.Point, HEq (K.inclusion.map z) z) ∧
      (fun x => (K.ambient.primitive (K.inclusion.map (P.inclusion x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (K.inclusion.map ∘ P.inclusion) x)) = α := by
  obtain ⟨C, δ, hδ, hemb, hC, hb, hinv, hzero, L, P,
    hP, _, _, _, hcylinder, hglobal, _, _⟩ :=
    exists_nativeLiouvillePresentation_on_quotient α hα hnd hout
  let K := completion hδ C hemb hC hb hinv hzero α hα L hglobal hcylinder
  obtain ⟨K', hambient, hprimitive, hinclusion⟩ := exists_completion_on_equal_native_domain
    P ⟨compactDomain hδ C hemb hC hb hinv hzero, L⟩ hP K rfl HEq.rfl (fun _ => HEq.rfl)
  exact ⟨P, K', hambient, hprimitive, hinclusion, completion_native_primitive P K'⟩

end FsFltz.Geometry.IntrinsicLiouville
