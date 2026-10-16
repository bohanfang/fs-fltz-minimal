import FsFltz.Geometry.IntrinsicLiouvilleBoundaryFamily
import FsFltz.Geometry.FamilyLiouvilleCollar
import Mathlib.Topology.LocalAtTarget

/-!
# One uniform native collar for a jointly smooth primitive family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The family flow on the constructed fixed presentation is restricted to its
inward half and returned to the original native manifold. Its joint embedding
uses the interval's relative topology, including the parameter endpoints.
The slice equations refer to the actual native exterior derivative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

namespace CompactDomain

/-- The native carrier atlas also detects smoothness within a set from the
actual ambient inclusion. This includes the one-sided seam of a collar. -/
theorem contMDiffWithinAt_iff_subtype_val {E H X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    {d : ℕ} [NeZero d] (D : CompactDomain d) {f : X → D.Point}
    {s : Set X} {x : X} :
    ContMDiffWithinAt I (𝓡∂ d) ∞ f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Model d) ∞ (Subtype.val ∘ f) s x := by
  constructor
  · intro hf
    exact D.contMDiff_subtype_val.contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    have hc : ContinuousWithinAt f s x :=
      Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hf.continuousWithinAt
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨hc, ?_⟩
    let c := D.halfSpaceChartAt (f x)
    have hcs : f x ∈ c.chart.source := D.mem_halfSpaceChartAt_source (f x)
    have hes : (f x).val ∈ c.extension.source := by rwa [c.source_eq] at hcs
    have he := c.extension.contMDiffOn_toFun.contMDiffAt
      (c.extension.open_source.mem_nhds hes)
    apply (he.comp_contMDiffWithinAt x hf).congr_of_eventuallyEq
    · filter_upwards [hc.eventually_mem (c.chart.open_source.mem_nhds hcs)] with y hy
      change (c.chart (f y)).val = c.extension (f y).val
      exact c.toFun_eq (f y) hy
    · exact c.toFun_eq (f x) hcs

/-- Restriction of the same joint two-sided collar to interval parameters
and the compact carrier is relatively open, including time zero. -/
theorem isOpenEmbedding_parameter_inwardCollar {k : ℕ} (D : CompactDomain (k + 1))
    {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
    (e : M ≃ₜ D.Point) (eB : B ≃ₜ D.boundary.Point)
    (J : TopologicalSpace.Opens ℝ) (hJ : parameterInterval ⊆ (J : Set ℝ))
    {δ : ℝ} (hδ : 0 < δ)
    (c : ℝ × (D.boundary.Point × ℝ) → D.extension.Point)
    (hemb : IsOpenEmbedding (fun p : {p : ℝ × (D.boundary.Point × ℝ) //
      p ∈ (J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)} => (p.val.1, c p.val)))
    (hside : ∀ (t : Parameter) b r, r ∈ Ioo (-δ) δ →
      (c (t.val, (b, r)) ∈ D.carrier ↔ r ≤ 0)) :
    ∃ C : Parameter → (Ico 0 δ ×ˢ (univ : Set B)) → M,
      (∀ t p, (e (C t p)).val = c (t.val, (eB p.val.2, -p.val.1))) ∧
      IsOpenEmbedding (fun p : Ico 0 δ ×ˢ (univ : Set (Parameter × B)) =>
        (p.val.2.1, C p.val.2.1 ⟨(p.val.1, p.val.2.2), p.property.1, mem_univ _⟩)) := by
  let R := (J : Set ℝ) ×ˢ ((univ : Set D.boundary.Point) ×ˢ Ioo (-δ) δ)
  let S := parameterInterval ×ˢ D.carrier
  let f : R → ℝ × D.extension.Point := fun p => (p.val.1, c p.val)
  have htime (s : ℝ) (hs : s ∈ Ico 0 δ) : -s ∈ Ioo (-δ) δ := by
    constructor <;> linarith [hs.1, hs.2]
  let A : (Ico 0 δ ×ˢ (univ : Set (Parameter × B))) ≃ₜ (f ⁻¹' S) :=
    { toFun := fun p =>
        ⟨⟨(p.val.2.1.val, (eB p.val.2.2, -p.val.1)),
          hJ p.val.2.1.property, mem_univ _, htime _ p.property.1⟩,
          p.val.2.1.property,
          (hside p.val.2.1 _ _ (htime _ p.property.1)).mpr (neg_nonpos.mpr p.property.1.1)⟩
      invFun := fun p =>
        ⟨(-p.val.val.2.2, (⟨p.val.val.1, p.property.1⟩, eB.symm p.val.val.2.1)),
          ⟨neg_nonneg.mpr ((hside ⟨p.val.val.1, p.property.1⟩ _ _
            p.val.property.2.2).mp p.property.2), neg_lt.mpr p.val.property.2.2.1⟩,
          mem_univ _⟩
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let H : S ≃ₜ Parameter × M :=
    { toFun := fun p => (⟨p.val.1, p.property.1⟩, e.symm ⟨p.val.2, p.property.2⟩)
      invFun := fun p => ⟨(p.1.val, (e p.2).val), p.1.property, (e p.2).property⟩
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let C : Parameter → (Ico 0 δ ×ˢ (univ : Set B)) → M := fun t p =>
    e.symm ⟨c (t.val, (eB p.val.2, -p.val.1)),
      (hside t _ _ (htime _ p.property.1)).mpr (neg_nonpos.mpr p.property.1.1)⟩
  refine ⟨C, ?_, ?_⟩
  · intro t p
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · exact H.isOpenEmbedding.comp ((hemb.restrictPreimage S).comp A.isOpenEmbedding)

end CompactDomain

/-- A parameter-preserving joint open embedding restricts to an open
embedding on each parameter fiber, with the relative fiber topology. -/
theorem isOpenEmbedding_parameter_slice {T X Y : Type*}
    [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    (c : T → X → Y)
    (hc : IsOpenEmbedding (fun p : T × X => (p.1, c p.1 p.2))) (t : T) :
    IsOpenEmbedding (c t) := by
  let f : T × X → T × Y := fun p => (p.1, c p.1 p.2)
  let S : Set (T × Y) := {p | p.1 = t}
  let A : X ≃ₜ (f ⁻¹' S) :=
    { toFun := fun x => ⟨(t, x), rfl⟩
      invFun := fun p => p.val.2
      left_inv := fun _ => rfl
      right_inv := by intro p; apply Subtype.ext; exact Prod.ext p.property.symm rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let H : S ≃ₜ Y :=
    { toFun := fun p => p.val.2
      invFun := fun y => ⟨(t, y), rfl⟩
      left_inv := by intro p; apply Subtype.ext; exact Prod.ext p.property.symm rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact H.isOpenEmbedding.comp ((hc.restrictPreimage S).comp A.isOpenEmbedding)

namespace IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original joint primitive data produce one native half collar whose
parameter-preserving map is an open embedding. The same collar solves the
native inward ODE and has smooth slice inverse germs. Its real-parameter
extension on the fixed source-derived presentation is retained, together
with joint local diffeomorphism germs for that exact extension. -/
theorem exists_uniform_native_joint_collar
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
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
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val))) :
    ∃ (δ : ℝ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M),
      0 < δ ∧
      IsOpenEmbedding (fun p : Ico 0 δ ×ˢ (univ : Set (Parameter × IntrinsicBoundary.Point k M)) =>
        (p.val.2.1, C p.val.2.1 (p.val.1, p.val.2.2))) ∧
      (∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
        (C t) (Ico 0 δ ×ˢ univ)) ∧
      (∀ t b, C t (0, b) = b.val) ∧
      (∀ t b s, s ∈ Ico 0 δ →
        ((𝓡∂ (k + 1)).IsBoundaryPoint (C t (s, b)) ↔ s = 0)) ∧
      (∀ t, IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C t p.val)) ∧
      (∀ t p, p ∈ Ico 0 δ ×ˢ univ →
        ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
          ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
            ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C t q) = q) ∧
      (∀ t b, IsMIntegralCurveOn (fun s => C t (s, b))
        (fun x => -liouvilleVector (α t) (exteriorDerivative (α t)) x) (Ico 0 δ)) ∧
      ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
        (eB : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.boundary)
        (c : ℝ × (D.boundary.Point × ℝ) → D.extension.Point)
        (J : TopologicalSpace.Opens ℝ),
        ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
        IsClosedEmbedding i ∧
        (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
        HasNativeCoordinateExtensions (k := k) D.extension i ∧
        ContMDiff ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model (k + 1)) ∞ c ∧
        parameterInterval ⊆ (J : Set ℝ) ∧
        IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞
          (fun p : ℝ × (D.boundary.Point × ℝ) => (p.1, c p))
          ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
        ∀ t p, p ∈ Ico 0 δ ×ˢ univ → i (C t p) = c (t.val, (eB p.2, -p.1)) := by
  obtain ⟨D, i, e, L, eB, he, hi, hiemb, hbij, hrange, hfrontier,
      hL, hfieldSmooth, hpull, hderiv, hfield, hglobal, hcompletion, hcoord, hB, hBform⟩ :=
    exists_liouvilleFamily_with_native_boundary_presentation_and_coordinates α hα hnd hout
  obtain ⟨U, J, δ, F, hU, hJ, hδ, hF, hfst, hlocal, hc, hcp,
      hzero, hinj, hdiff, hemb, hside, hprimitive⟩ :=
    D.exists_liouvilleFamily_localCollar L hL
  let c := D.boundaryFamilyFlow F
  obtain ⟨C₀, hC₀, hC₀emb⟩ := D.isOpenEmbedding_parameter_inwardCollar
    e.toHomeomorph eB.toHomeomorph J hJ hδ c hemb hside
  let S : Set (ℝ × IntrinsicBoundary.Point k M) := Ico 0 δ ×ˢ univ
  let C : Parameter → ℝ × IntrinsicBoundary.Point k M → M := fun t p =>
    if hp : p ∈ S then C₀ t ⟨p, hp⟩ else p.2.val
  have hCeq (t : Parameter) (p : ℝ × IntrinsicBoundary.Point k M) (hp : p ∈ S) :
      i (C t p) = c (t.val, (eB p.2, -p.1)) := by
    rw [← he]
    dsimp only [C]
    rw [dite_eq_left hp]
    exact hC₀ t ⟨p, hp⟩
  have htime (s : ℝ) (hs : s ∈ Ico 0 δ) : -s ∈ Ioo (-δ) δ := by
    constructor <;> linarith [hs.1, hs.2]
  have hCsmooth (t : Parameter) : ContMDiffOn
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t) S := by
    let g : ℝ × IntrinsicBoundary.Point k M → D.Point := fun p => e (C t p)
    have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
        (𝓡∂ (k + 1)) ∞ g S := by
      intro p hp
      apply D.contMDiffWithinAt_iff_subtype_val.mpr
      have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
          𝓘(ℝ, Model (k + 1)) ∞
          (fun q : ℝ × IntrinsicBoundary.Point k M => c (t.val, (eB q.2, -q.1))) :=
        hc.comp (contMDiff_const.prodMk
          ((eB.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst.neg))
      exact (hs p).contMDiffWithinAt.congr
        (fun q hq => (he (C t q)).trans (hCeq t q hq))
        ((he (C t p)).trans (hCeq t p hp))
    have hh := e.symm.contMDiff.comp_contMDiffOn hg
    simpa only [Function.comp_def, g, e.symm_apply_apply] using hh
  have hCzero (t : Parameter) (b : IntrinsicBoundary.Point k M) : C t (0, b) = b.val := by
    apply hiemb.injective
    rw [hCeq t (0, b) ⟨⟨le_rfl, hδ⟩, mem_univ _⟩]
    simpa only [c, neg_zero] using (hzero t.val (eB b)).trans (hB b)
  have hCb (t : Parameter) (b : IntrinsicBoundary.Point k M) (s : ℝ)
      (hs : s ∈ Ico 0 δ) :
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t (s, b)) ↔ s = 0 := by
    constructor
    · intro hb
      let y : IntrinsicBoundary.Point k M := ⟨C t (s, b), hb⟩
      have heq : c (t.val, (eB b, -s)) = c (t.val, (eB y, 0)) := by
        exact (hCeq t (s, b) ⟨hs, mem_univ _⟩).symm.trans
          ((hB y).symm.trans (hzero t.val (eB y)).symm)
      have hh := @hinj (t.val, (eB b, -s)) ⟨hJ t.property, mem_univ _, htime s hs⟩
        (t.val, (eB y, 0))
        ⟨hJ t.property, mem_univ _, neg_lt_zero.mpr hδ, hδ⟩ (Prod.ext rfl heq)
      have hn : -s = 0 := congrArg (fun p : ℝ × (D.boundary.Point × ℝ) => p.2.2) hh
      exact neg_eq_zero.mp hn
    · rintro rfl
      rw [hCzero]
      exact b.property
  have hjoint : IsOpenEmbedding
      (fun p : Ico 0 δ ×ˢ (univ : Set (Parameter × IntrinsicBoundary.Point k M)) =>
        (p.val.2.1, C p.val.2.1 (p.val.1, p.val.2.2))) := by
    convert hC₀emb using 1
    funext p
    dsimp only [C]
    rw [dite_eq_left (show (p.val.1, p.val.2.2) ∈ S from ⟨p.property.1, mem_univ _⟩)]
  have hCemb (t : Parameter) : IsOpenEmbedding (fun p : S => C t p.val) := by
    let A : Parameter × S ≃ₜ (Ico 0 δ ×ˢ (univ : Set (Parameter × IntrinsicBoundary.Point k M))) :=
      { toFun := fun p => ⟨(p.2.val.1, (p.1, p.2.val.2)), p.2.property.1, mem_univ _⟩
        invFun := fun p => (p.val.2.1, ⟨(p.val.1, p.val.2.2), p.property.1, mem_univ _⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isOpenEmbedding_parameter_slice (fun t (p : S) => C t p.val)
      (hjoint.comp A.isOpenEmbedding) t
  have hCinv (t : Parameter) (p : ℝ × IntrinsicBoundary.Point k M) (hp : p ∈ S) :
      ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
          ∀ᶠ q in 𝓝[S] p, g (C t q) = q := by
    let z : ℝ × (D.boundary.Point × ℝ) := (t.val, (eB p.2, -p.1))
    obtain ⟨d, hzd, hd⟩ := hdiff ⟨z, hJ t.property, mem_univ _, htime p.1 hp.1⟩
    let R : (ℝ × (D.boundary.Point × ℝ)) → ℝ × IntrinsicBoundary.Point k M :=
      fun q => (-q.2.2, eB.symm q.2.1)
    let g : M → ℝ × IntrinsicBoundary.Point k M := fun x => R (d.symm (t.val, i x))
    have hR : ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ R :=
      (contMDiff_snd.comp contMDiff_snd).neg.prodMk
        (eB.symm.contMDiff.comp (contMDiff_fst.comp contMDiff_snd))
    have hdtarget : (t.val, i (C t p)) ∈ d.target := by
      rw [hCeq t p hp]
      change D.boundaryFamilyFlowWithParameter F z ∈ d.target
      rw [hd hzd]
      exact d.map_source hzd
    refine ⟨g, ?_, ?_⟩
    · exact hR.contMDiffAt.comp (C t p)
        ((d.contMDiffOn_invFun.contMDiffAt (d.open_target.mem_nhds hdtarget)).comp
          (C t p) (contMDiff_const.prodMk hi).contMDiffAt)
    · have hsource : ∀ᶠ q in 𝓝[S] p,
          (t.val, (eB q.2, -q.1)) ∈ d.source := by
        have hmap : Continuous (fun q : ℝ × IntrinsicBoundary.Point k M =>
            (t.val, (eB q.2, -q.1))) := by fun_prop
        exact mem_nhdsWithin_of_mem_nhds
          (hmap.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hzd))
      filter_upwards [self_mem_nhdsWithin, hsource] with q hq hqd
      dsimp only [g]
      rw [hCeq t q hq]
      change R (d.symm (D.boundaryFamilyFlowWithParameter F (t.val, (eB q.2, -q.1)))) = q
      rw [hd hqd]
      change R (d.toPartialEquiv.symm (d.toPartialEquiv (t.val, (eB q.2, -q.1)))) = q
      rw [d.toPartialEquiv.left_inv hqd]
      simp only [R, neg_neg, eB.symm_apply_apply, Prod.mk.eta]
  have hCode (t : Parameter) (b : IntrinsicBoundary.Point k M) :
      IsMIntegralCurveOn (fun s => C t (s, b))
        (fun x => -liouvilleVector (α t) (exteriorDerivative (α t)) x) (Ico 0 δ) := by
    intro s hs
    have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) ∞
        (fun u => C t (u, b)) (Ico 0 δ) :=
      (hCsmooth t).comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
        (fun u hu => ⟨hu, mem_univ _⟩)
    have hdγ := (hγ s hs).mdifferentiableWithinAt (by simp) |>.hasMFDerivWithinAt
    have hdc := (hlocal t (D.boundaryInclusion.map (eB b))
      (hU ⟨t.property, D.boundaryInclusion_mem_carrier (eB b)⟩) (-s) (htime s hs)).2.2
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (k + 1))
      (fun u => c (t.val, (eB b, u))) (-s)
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (D.extension.liouvilleVector (L t).primitive (c (t.val, (eB b, -s))))) at hdc
    have hmem : c (t.val, (eB b, -s)) ∈ D.carrier :=
      (hside t (eB b) (-s) (htime s hs)).mpr (neg_nonpos.mpr hs.1)
    rw [← (L t).field_eq_liouvilleVector _ hmem] at hdc
    have hdneg := hdc.comp s (hasMFDerivAt_id s).neg
    have hiγ := (hi (C t (s, b))).mdifferentiableAt (by simp) |>.hasMFDerivAt
    have hcomp := hiγ.comp_hasMFDerivWithinAt s hdγ
    have heq : (fun u => i (C t (u, b))) =ᶠ[𝓝[Ico 0 δ] s]
        (fun u => c (t.val, (eB b, -u))) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hCeq t (u, b) ⟨hu, mem_univ _⟩
    have hds := hdneg.hasMFDerivWithinAt.congr_of_eventuallyEq heq
      (hCeq t (s, b) ⟨hs, mem_univ _⟩)
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Ico 0 δ) s :=
      uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr ((uniqueDiffOn_Ico 0 δ) s hs)
    have hder := hu.eq hcomp hds
    apply hdγ.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    apply (hbij (C t (s, b))).1
    have hv := congrArg (fun A : ℝ →L[ℝ] Model (k + 1) => A r) hder
    change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i (C t (s, b))
      (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ (k + 1))
        (fun u => C t (u, b)) (Ico 0 δ) s r) =
      (-r) • (L t).field (c (t.val, (eB b, -s))) at hv
    rw [← hCeq t (s, b) ⟨hs, mem_univ _⟩, hfield] at hv
    change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i (C t (s, b))
      (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ (k + 1))
        (fun u => C t (u, b)) (Ico 0 δ) s r) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i (C t (s, b))
        (r • -liouvilleVector (α t) (exteriorDerivative (α t)) (C t (s, b)))
    rw [map_smul, map_neg, smul_neg]
    simpa only [neg_smul] using hv
  exact ⟨δ, C, hδ, hjoint, hCsmooth, hCzero, hCb, hCemb, hCinv,
    hCode, D, i, eB, c, J, hi, hiemb, hbij, hcoord, hc, hJ, hdiff, hCeq⟩

end IntrinsicLiouville
end FsFltz.Geometry
