import FsFltz.Geometry.IntrinsicPrimitiveFamilyExtension

/-!
# Joint native primitive gluing on one fixed spatial presentation

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. A reference primitive constructs the spatial
collar quotient once. The entire joint family extends on that presentation
by pulling coordinate germs through its actual smooth coordinate extensions
and gluing on the closed product of the parameter interval with the carrier.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Actual local extensions of native source-chart coordinates on one fixed
spatial presentation. Agreement holds on the whole native carrier in each
open patch, including its boundary; this is concrete local extension data. -/
def HasNativeCoordinateExtensions {d : ℕ} (N : SmoothManifold d)
    (i : M → N.Point) : Prop :=
  ∀ x : M,
    ∃ (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
      (O : Set N.Point) (Q : N.Point → Model (k + 1)),
      e ∈ atlas (EuclideanHalfSpace (k + 1)) M ∧ IsOpen O ∧ i x ∈ O ∧
      ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) ∞ Q O ∧
      ∀ y, i y ∈ O → y ∈ e.source ∧ Q (i y) = e.extend (𝓡∂ (k + 1)) y

private theorem form_eq_of_comp_eq {d : ℕ} (N : SmoothManifold d)
    (x : N.Point) (A B : N.Tangent x [⋀^Fin 1]→L[ℝ] ℝ)
    (T : Model (k + 1) →L[ℝ] N.Tangent x) (hT : Function.Surjective T)
    (h : A.compContinuousLinearMap T = B.compContinuousLinearMap T) : A = B := by
  ext vs
  choose ws hws using fun j => hT (vs j)
  have he := congrArg (fun C => C ws) h
  simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hws] using he

/-- Joint coefficient germs extend to one family on a fixed boundaryless
presentation whose actual source charts have smooth extensions. The chart
extensions may differ outside the native carrier. -/
theorem exists_primitiveFamily_on_fixed_presentation
    (N : SmoothManifold (k + 1)) (i : M → N.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hemb : Topology.IsClosedEmbedding i)
    (hbij : ∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1))
      𝓘(ℝ, Model (k + 1)) i x))
    (hcoord : ∀ x : M,
      ∃ (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
        (O : Set N.Point) (Q : N.Point → Model (k + 1)),
        e ∈ atlas (EuclideanHalfSpace (k + 1)) M ∧ IsOpen O ∧ i x ∈ O ∧
        ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q O ∧
        ∀ y, i y ∈ O → y ∈ e.source ∧ Q (i y) = e.extend (𝓡∂ (k + 1)) y)
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α) :
    ∃ lam : Parameter → N.Form 1,
      N.IsSmoothIntervalFormFamily lam ∧
      ∀ t, (fun x => (lam t (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t := by
  classical
  let T (x : M) : Model (k + 1) ≃L[ℝ] Model (k + 1) :=
    (LinearEquiv.ofBijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x).toLinearMap
      (hbij x)).toContinuousLinearEquiv
  let f : (p : ℝ × N.Point) → N.Tangent p.2 [⋀^Fin 1]→L[ℝ] ℝ := fun p =>
    if ht : p.1 ∈ parameterInterval then
      if hx : ∃ x : M, i x = p.2 then
        (α ⟨p.1, ht⟩ hx.choose).compContinuousLinearMap (T hx.choose).symm.toContinuousLinearMap
      else 0
    else 0
  have hfpull (t : Parameter) (x : M) :
      (f (t.val, i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α t x := by
    have hx : ∃ y : M, i y = i x := ⟨x, rfl⟩
    have hchoose : hx.choose = x := hemb.injective hx.choose_spec
    dsimp only [f]
    rw [dite_eq_left (show t.val ∈ parameterInterval from t.property), dite_eq_left hx, hchoose]
    ext vs
    change α t x (fun j => (T x).symm ((T x) (vs j))) = α t x vs
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  let A := parameterInterval ×ˢ range i
  have hlocal : ∀ p ∈ A,
      ∃ U, IsOpen U ∧ p ∈ U ∧ ∃ g : ℝ → N.Form 1,
        N.IsSmoothFormFamilyOn g U ∧ ∀ q ∈ U ∩ A, g q.1 q.2 = f q := by
    rintro ⟨s, z⟩ ⟨hs, x, rfl⟩
    let t : Parameter := ⟨s, hs⟩
    obtain ⟨e, O, Q, he, hO, hxO, hQ, hagree⟩ := hcoord x
    have hxsource := (hagree x hxO).1
    obtain ⟨V, β, hV, hpV, hβ, hβeq⟩ := hα e he t x hxsource
    let P : ℝ × N.Point → ℝ × Model (k + 1) := fun p => (p.1, Q p.2)
    let U := (univ ×ˢ O) ∩ P ⁻¹' V
    have hP : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
        𝓘(ℝ, ℝ × Model (k + 1)) ∞ P (univ ×ˢ O) :=
      contMDiff_fst.contMDiffOn.prodMk_space
        (hQ.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
    have hU : IsOpen U := hP.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hO) hV
    have hpU : (s, i x) ∈ U := ⟨⟨mem_univ _, hxO⟩, by
      change (s, Q (i x)) ∈ V
      rw [(hagree x hxO).2]
      exact hpV⟩
    let g : ℝ → N.Form 1 := fun s z => (β (s, Q z)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) Q z)
    have hg : N.IsSmoothFormFamilyOn g U :=
      N.isSmoothFormFamilyOn_modelPullback Q hO hQ β hV hβ
    refine ⟨U, hU, hpU, g, hg, ?_⟩
    rintro ⟨s', z'⟩ ⟨hqU, hs', y, rfl⟩
    let t' : Parameter := ⟨s', hs'⟩
    have hyO : i y ∈ O := hqU.1.2
    obtain ⟨hysource, hyQ⟩ := hagree y hyO
    have hQieq : Q ∘ i =ᶠ[𝓝 y] e.extend (𝓡∂ (k + 1)) := by
      filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds (hO.mem_nhds hyO)] with w hw
      exact (hagree w hw).2
    have hdQ := mfderiv_comp y
      ((hQ.contMDiffAt (hO.mem_nhds hyO)).mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))
    have hdE := hQieq.mfderiv_eq (I := 𝓡∂ (k + 1)) (I' := 𝓘(ℝ, Model (k + 1)))
    have hder : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) Q (i y)).comp
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i y) = chartTangentMap e y :=
      hdQ.symm.trans hdE
    have hyTarget : e.extend (𝓡∂ (k + 1)) y ∈ (e.extend (𝓡∂ (k + 1))).target :=
      (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hysource)
    have hβval : β (s', Q (i y)) = formInChart e (α t') (e.extend (𝓡∂ (k + 1)) y) := by
      rw [hyQ]
      have h := hqU.2
      change (s', Q (i y)) ∈ V at h
      rw [hyQ] at h
      exact hβeq t' _ hyTarget h
    have hgpull : (g s' (i y)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i y) = α t' y := by
      change (β (s', Q (i y))).compContinuousLinearMap
        ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) Q (i y)).comp
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i y)) = _
      rw [hder, hβval]
      exact formInChart_comp_chartTangentMap he (α t') hysource
    apply form_eq_of_comp_eq N (i y) _ _ _ (hbij y).2
    exact hgpull.trans (hfpull t' y).symm
  obtain ⟨lam, hlam, heq⟩ := N.exists_smoothFormFamily_extension_of_closed
    (isClosed_Icc.prod hemb.isClosed_range) hlocal
  refine ⟨fun t => lam t.val, ⟨lam, hlam, fun _ => rfl⟩, ?_⟩
  intro t
  funext x
  change (lam t.val (i x)).compContinuousLinearMap _ = _
  have he := heq (t.val, i x) ⟨t.property, mem_range_self x⟩
  change lam t.val (i x) = f (t.val, i x) at he
  rw [he]
  exact hfpull t x

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- One source-derived spatial presentation extends the entire native
primitive family jointly. Only the reference slice's Liouville conditions
are used to choose the collar; no off-interval geometric inequality or
preselected family extension is assumed. -/
theorem exists_compactDomain_with_native_primitiveFamily_and_coordinates
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hndZero : ∀ x, Nondegenerate (exteriorDerivative (α parameterZero)) x)
    (houtZero : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α parameterZero) (exteriorDerivative (α parameterZero)) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
      (lam : Parameter → D.extension.Form 1),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothIntervalFormFamily lam ∧
      (∀ t, (fun x => (lam t (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t) ∧ HasNativeCoordinateExtensions (k := k) D.extension i := by
  have hαZero := hα.slice parameterZero
  obtain ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, _, _⟩ :=
    exists_topological_extension_with_primitive_collar
      (α parameterZero) hαZero hndZero houtZero
  let c := fun p : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M) => C p.val
  have hb : ∀ p : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0 :=
    fun p => hboundary p.val.2 p.val.1 p.property.1
  let D := IntrinsicCollarGluing.compactDomain hδ C hemb hC hb hinv hzero
  let i : M → D.extension.Point := IntrinsicCollarGluing.original c
  have hi := IntrinsicCollarGluing.contMDiff_original hδ C hemb hC hb hinv hzero
  have hiemb := IntrinsicCollarGluing.isClosedEmbedding_original hδ c hemb
  have hibij := IntrinsicCollarGluing.bijective_mfderiv_original hδ C hemb hC hb hinv hzero
  have houtnorm (x : IntrinsicBoundary.Point k M) :
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt x).ambient) x.val
          (liouvilleVector (α parameterZero) (exteriorDerivative (α parameterZero)) x.val)) := by
    obtain ⟨rho, beta, hz, hs, hr, hbeta, heq, hp⟩ := houtZero x
    have hx : x.val ∈ (IntrinsicBoundary.chartAt x).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source x
      rwa [(IntrinsicBoundary.chartAt x).source_eq] at h
    have hn := (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt x).mem_atlas hx x.property rho hz hs hr hbeta heq
      (liouvilleVector (α parameterZero) (exteriorDerivative (α parameterZero)) x.val)).mp hp
    rw [normalDefiningFunction_derivative (IntrinsicBoundary.chartAt x).mem_atlas hx]
    exact neg_pos.mpr hn
  have hcoord : ∀ x : M,
      ∃ (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
        (O : Set D.extension.Point) (Q : D.extension.Point → Model (k + 1)),
        e ∈ atlas (EuclideanHalfSpace (k + 1)) M ∧ IsOpen O ∧ i x ∈ O ∧
        ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q O ∧
        ∀ y, i y ∈ O → y ∈ e.source ∧ Q (i y) = e.extend (𝓡∂ (k + 1)) y := by
    intro x
    rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · let u : IntrinsicInterior.Point k M := ⟨x, hx⟩
      obtain ⟨O, Q, hO, hxO, hQ, heq⟩ :=
        IntrinsicCollarGluing.exists_interior_coordinate_extension hδ C hemb hC hb hinv hzero u
      exact ⟨chartAt (EuclideanHalfSpace (k + 1)) x, O, Q,
        chart_mem_atlas _ x, hO, hxO, hQ, heq⟩
    · let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
      obtain ⟨O, Q, hO, hxO, hQ, heq⟩ :=
        IntrinsicCollarGluing.exists_boundary_coordinate_extension_of_primitive
          hδ C hemb hC hb hinv hzero (α parameterZero) hαZero hndZero b (houtnorm b) hode
      exact ⟨(IntrinsicBoundary.chartAt b).ambient, O, Q,
        (IntrinsicBoundary.chartAt b).mem_atlas, hO, hxO, hQ, heq⟩
  obtain ⟨lam, hlam, hpull⟩ :=
    exists_primitiveFamily_on_fixed_presentation D.extension i hi hiemb hibij hcoord α hα
  refine ⟨D, i,
    IntrinsicCollarGluing.originalDiffeomorph hδ C hemb hC hb hinv hzero,
    lam, fun _ => rfl, hi, hiemb, hibij, rfl, ?_, hlam, hpull, hcoord⟩
  exact IntrinsicCollarGluing.frontier_range_original hδ c hemb hb hzero

/-- Forgetting the produced coordinate extensions retains the original
primitive-family API on the same constructed spatial presentation. -/
theorem exists_compactDomain_with_native_primitiveFamily
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hndZero : ∀ x, Nondegenerate (exteriorDerivative (α parameterZero)) x)
    (houtZero : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α parameterZero) (exteriorDerivative (α parameterZero)) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
      (lam : Parameter → D.extension.Form 1),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothIntervalFormFamily lam ∧
      ∀ t, (fun x => (lam t (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t := by
  obtain ⟨D, i, e, lam, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, _⟩ :=
    exists_compactDomain_with_native_primitiveFamily_and_coordinates α hα hndZero houtZero
  exact ⟨D, i, e, lam, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull⟩

end FsFltz.Geometry.IntrinsicLiouville
