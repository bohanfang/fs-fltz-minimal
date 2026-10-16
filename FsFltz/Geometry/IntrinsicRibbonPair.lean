import FsFltz.Geometry.IntrinsicLiouvilleMapExtension
import FsFltz.Geometry.PairFamilyConstruction
import FsFltz.Geometry.ImmersionNeighborhood

/-!
# Native positive-dimensional ribbons on presented ambient boundaries

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. The native Liouville presentation extends the
prescribed ribbon map on a neighborhood of its entire compact carrier.
Its bijective inclusion differential transports native immersion and the
full primitive identity. An embedding neighborhood then supplies an actual
extended ribbon embedding, and constructed flow collars supply completions.

The ambient boundary is supplied as a compact-domain presentation. This is
a foundational producer, not the far-fiber pair, a completion marking onto a
specified ambient manifold, or the geometric comparison theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- A native embedding's immersion transfers to a smooth extension through
a carrier inclusion with bijective differential. -/
theorem injective_mfderiv_of_native_comp {d : ℕ}
    (F : SmoothManifold (k + 1)) (N : SmoothManifold d)
    (i : M → F.Point) (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hdi : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (g : F.Point → N.Point) (hg : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ g)
    (j : M → N.Point) (heq : ∀ x, g (i x) = j x)
    (hdj : ∀ x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) j x))
    (x : M) : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) g (i x)) := by
  have hd := mfderiv_comp (f := i) (g := g) x
    (hg.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  rw [show g ∘ i = j from funext heq] at hd
  intro v w hvw
  obtain ⟨a, ha⟩ := (hdi x).2 v
  obtain ⟨b, hb⟩ := (hdi x).2 w
  have hab : a = b := hdj x (by
    rw [hd]
    change (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) g (i x))
      ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) a) =
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) g (i x))
      ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) b)
    rw [ha, hb]
    exact hvw)
  exact ha.symm.trans (hab ▸ hb)

/-- Equality after native pullback determines the full extension one-form,
because the carrier inclusion differential is surjective. -/
theorem pullback_eq_of_native_comp {d : ℕ}
    (F : SmoothManifold (k + 1)) (N : SmoothManifold d)
    (i : M → F.Point) (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hdi : ∀ x, Function.Surjective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (g : F.Point → N.Point) (hg : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ g)
    (j : M → N.Point) (heq : ∀ x, g (i x) = j x)
    (η : N.Form 1) (lam : F.Form 1) (α : Form k M 1)
    (hlam : ∀ x, (lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x)
    (hη : ∀ x, (η (j x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) j x) = α x)
    (x : M) : F.pullback N g η (i x) = lam (i x) := by
  have hd := mfderiv_comp (f := i) (g := g) x
    (hg.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  rw [show g ∘ i = j from funext heq] at hd
  ext vs
  obtain ⟨v, hv⟩ := hdi x (vs 0)
  have he := congrArg (fun a => a (fun _ => v)) ((hη x).trans (hlam x).symm)
  rw [hd] at he
  change η (j x) (fun _ => (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) g (i x))
    ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) v)) =
    lam (i x) (fun _ => (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) v) at he
  rw [hv, ← heq x] at he
  have hvs : (fun _ : Fin 1 => vs 0) = vs := by
    funext t
    exact congrArg vs (Fin.eq_zero t).symm
  rw [hvs] at he
  simpa only [SmoothManifold.pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, Fin.eq_zero] using he

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- A native positive-dimensional Liouville ribbon and a native smooth
embedding into a supplied manifold construct an actual extension embedding.
The selected presentation retains the entire native compact ribbon, and the
primitive equality holds on its full tangent spaces. Only an open map
extension near the compact carrier is used, including for an empty ribbon. -/
theorem exists_liouvilleDomain_with_native_ribbon_embedding {d : ℕ}
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
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (N : SmoothManifold d) (j : M → N.Point)
    (hjs : IsLocallyExtendibleMap (k := k) (F := Model d) j)
    (hjinj : Function.Injective j)
    (hjimm : ∀ x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) j x))
    (η : N.Form 1)
    (hη : ∀ x, (η (j x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) j x) = α x) :
    ∃ (F : LiouvilleDomain (k + 1)) (i : M → F.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M F.domain.Point ∞)
      (q : F.domain.extension.SmoothEmbedding N),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = F.domain.carrier ∧ (∀ x, q.map (i x) = j x) ∧
      (∀ x, (F.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x) ∧
      ∀ x ∈ F.domain.carrier, F.domain.extension.pullback N q.map η x =
        F.liouville.primitive x := by
  obtain ⟨F, i, e, he, hi, _, hdi, hrange, _, hpull, _, _, _, _, _, hmap⟩ :=
    exists_liouvilleDomain_with_native_presentation_and_map_extensions α hα hnd hout
  obtain ⟨W, hW, g, hg, heq⟩ := hmap d N j hjs
  have hFW : F.domain.carrier ⊆ W := hrange ▸ hW
  let F₁ := F.restrict W hFW
  let i₁ : M → F₁.domain.extension.Point := fun x => ⟨i x, hW ⟨x, rfl⟩⟩
  have hi₁ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i₁ :=
    (ContMDiff.subtypeVal_comp_iff W i₁).mp hi
  have hdi₁ (x : M) : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i₁ x =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x := by
    have hd := mfderiv_comp (f := i₁)
      (g := (Subtype.val : W → F.domain.extension.Point)) x
      ((F.domain.extension.restrictInclusion W).map.contMDiff.mdifferentiableAt (by simp))
      (hi₁.mdifferentiableAt (by simp))
    erw [F.domain.extension.mfderiv_restrict_val W (i₁ x)] at hd
    exact hd.symm
  have hbij₁ (x : M) : Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i₁ x) := by
    rw [hdi₁]
    exact hdi x
  have hrange₁ : range i₁ = F₁.domain.carrier := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change i x ∈ F.domain.carrier
      rw [← hrange]
      exact mem_range_self x
    · intro hy
      obtain ⟨x, hx⟩ : y.val ∈ range i := hrange ▸ hy
      exact ⟨x, Subtype.ext hx⟩
  have hgimm : ∀ y ∈ F₁.domain.carrier, Function.Injective
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) g y) := by
    intro y hy
    rw [← hrange₁] at hy
    obtain ⟨x, rfl⟩ := hy
    exact injective_mfderiv_of_native_comp F₁.domain.extension N i₁ hi₁ hbij₁
      g hg j heq hjimm x
  have hginj : InjOn g F₁.domain.carrier := by
    intro y hy z hz hyz
    rw [← hrange₁] at hy hz
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact congrArg i₁ (hjinj ((heq a).symm.trans (hyz.trans (heq b))))
  obtain ⟨U, hU, q, _, hq⟩ := F₁.domain.extension.exists_smooth_embedding_neighborhood N
    F₁.domain.carrier F₁.domain.compact g univ isOpen_univ (subset_univ _)
    hg.contMDiffOn hginj hgimm
  let F₂ := F₁.restrict U hU
  let i₂ : M → F₂.domain.extension.Point := fun x => ⟨i₁ x, hU (hrange₁ ▸ mem_range_self x)⟩
  have hi₂ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i₂ :=
    (ContMDiff.subtypeVal_comp_iff U i₂).mp hi₁
  have hdi₂ (x : M) : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i₂ x =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i₁ x := by
    have hd := mfderiv_comp (f := i₂)
      (g := (Subtype.val : U → F₁.domain.extension.Point)) x
      ((F₁.domain.extension.restrictInclusion U).map.contMDiff.mdifferentiableAt (by simp))
      (hi₂.mdifferentiableAt (by simp))
    erw [F₁.domain.extension.mfderiv_restrict_val U (i₂ x)] at hd
    exact hd.symm
  have hbij₂ (x : M) : Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i₂ x) := by
    rw [hdi₂]
    exact hbij₁ x
  have hrange₂ : range i₂ = F₂.domain.carrier := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change i₁ x ∈ F₁.domain.carrier
      exact hrange₁ ▸ mem_range_self x
    · intro hy
      obtain ⟨x, hx⟩ : y.val ∈ range i₁ := hrange₁ ▸ hy
      exact ⟨x, Subtype.ext hx⟩
  let := F₁.domain.halfSpaceChartedSpace
  let := F₂.domain.halfSpaceChartedSpace
  let e₂ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M F₂.domain.Point ∞ :=
    (e.trans (F.domain.restrictPointDiffeomorph W hFW).symm).trans
      (F₁.domain.restrictPointDiffeomorph U hU).symm
  have he₂ (x : M) : (e₂ x).val = i₂ x := by
    apply Subtype.ext
    apply Subtype.ext
    exact he x
  have hqj (x : M) : q.map (i₂ x) = j x := (hq _).trans (heq x)
  have hpull₂ (x : M) : (F₂.liouville.primitive (i₂ x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i₂ x) = α x := by
    rw [F₁.liouville.restrict_primitive U hU, F.liouville.restrict_primitive W hFW,
      hdi₂, hdi₁]
    exact congrFun hpull x
  refine ⟨F₂, i₂, e₂, q, he₂, hi₂, hbij₂, hrange₂, hqj, hpull₂, ?_⟩
  intro y hy
  rw [← hrange₂] at hy
  obtain ⟨x, rfl⟩ := hy
  exact pullback_eq_of_native_comp F₂.domain.extension N i₂ hi₂ (fun x => (hbij₂ x).2)
    q.map q.map.contMDiff j hqj η F₂.liouville.primitive α hpull₂ hη x

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.LiouvilleDomain.FlowCollar

set_option backward.isDefEq.respectTransparency false

/-- The constructed collar localization retains the entire original native
compact domain by its two actual open-restriction diffeomorphisms. -/
def originalPointDiffeomorph {d : ℕ} [NeZero d] {D : LiouvilleDomain d}
    (C : FlowCollar D) : Diffeomorph (𝓡∂ d) (𝓡∂ d)
      C.localizedDomain.domain.Point D.domain.Point ∞ := by
  let := D.neighborhoodDomain.halfSpaceChartedSpace
  let := C.localizedDomain.domain.halfSpaceChartedSpace
  let := (D.neighborhoodDomain.restrict C.neighborhood C.carrier_subset_neighborhood).halfSpaceChartedSpace
  let := (D.domain.restrict D.symplecticNeighborhood D.carrier_subset_symplecticNeighborhood).halfSpaceChartedSpace
  exact (D.neighborhoodDomain.restrictPointDiffeomorph C.neighborhood
    C.carrier_subset_neighborhood).trans
      (D.domain.restrictPointDiffeomorph D.symplecticNeighborhood
        D.carrier_subset_symplecticNeighborhood)

@[simp] theorem originalPointDiffeomorph_val {d : ℕ} [NeZero d] {D : LiouvilleDomain d}
    (C : FlowCollar D) (x : C.localizedDomain.domain.Point) :
    (C.originalPointDiffeomorph x).val = x.val.val.val := rfl

end FsFltz.Geometry.LiouvilleDomain.FlowCollar

namespace FsFltz.Geometry.WitnessedPair

set_option backward.isDefEq.respectTransparency false

/-- The actual pair primitive, pulled back through a native compact ribbon
presentation, is the prescribed native primitive on every tangent vector. -/
theorem native_ribbon_primitive {n k : ℕ} [NeZero (2 * n - 2)] {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M]
    (P : WitnessedPair n)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞)
    (α : IntrinsicLiouville.Form k M 1) (j : M → P.ambientDomain.domain.boundary.Point)
    (he : ∀ x, P.ribbonEmbedding.map (e x).val = j x)
    (hα : ∀ x, (P.witness (j x) • P.ambientDomain.domain.boundaryForm
      P.ambientDomain.liouville.primitive (j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) j x) = α x) :
    ∀ x, (P.ribbonDomain.liouville.primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (e y).val) x) = α x := by
  let i : M → P.ribbonDomain.domain.extension.Point := fun y => (e y).val
  have hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i :=
    P.ribbonDomain.domain.contMDiff_subtype_val.comp e.contMDiff
  intro x
  have hd := mfderiv_comp (f := i) (g := P.ribbonEmbedding.map) x
    (P.ribbonEmbedding.map.contMDiff.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  rw [show P.ribbonEmbedding.map ∘ i = j from funext he] at hd
  rw [← P.ribbon_primitive (e x).val (e x).property, ← hα x]
  ext vs
  change (P.witness (P.ribbonEmbedding.map (e x).val) •
      P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive
        (P.ribbonEmbedding.map (e x).val))
      (fun a => mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n - 1))
        P.ribbonEmbedding.map (e x).val
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x (vs a))) =
    (P.witness (j x) • P.ambientDomain.domain.boundaryForm
      P.ambientDomain.liouville.primitive (j x))
      (fun a => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) j x (vs a))
  rw [he]
  apply congrArg (P.witness (j x) • P.ambientDomain.domain.boundaryForm
      P.ambientDomain.liouville.primitive (j x))
  funext a
  exact congrArg (fun A => A (vs a)) hd.symm

/-- The full embedded core is the image of the native all-forward-time core
for this same constructed completion and carrier inclusion. -/
theorem embeddedCore_eq_native_image {n : ℕ} {M : Type} (P : WitnessedPair n)
    (e : M ≃ P.ribbonDomain.domain.Point)
    (j : M → P.ambientDomain.domain.boundary.Point)
    (he : ∀ x, P.ribbonEmbedding.map (e x).val = j x) :
    P.embeddedCore = j '' {x | ∀ t : ℝ, 0 ≤ t →
      P.ribbonCompletion.ambient.completeFlow.flow t (P.ribbonCompletion.inclusion.map (e x).val) ∈
        range (fun y => P.ribbonCompletion.inclusion.map (e y).val)} := by
  have hrange : range (fun y => P.ribbonCompletion.inclusion.map (e y).val) =
      P.ribbonCompletion.inclusion.map '' P.ribbonDomain.domain.carrier := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(e x).val, (e x).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
      exact ⟨x, congrArg (fun w => P.ribbonCompletion.inclusion.map w.val) hx⟩
  rw [hrange]
  ext y
  constructor
  · rintro ⟨z, ⟨hz, hf⟩, hzy⟩
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    have hv : (e x).val = z := congrArg Subtype.val hx
    refine ⟨x, ?_, (he x).symm.trans (hv ▸ hzy)⟩
    change ∀ t : ℝ, 0 ≤ t →
      P.ribbonCompletion.ambient.completeFlow.flow t (P.ribbonCompletion.inclusion.map (e x).val) ∈ _
    simpa only [hv] using hf
  · rintro ⟨x, hx, hxy⟩
    exact ⟨(e x).val, ⟨(e x).property, hx⟩, (he x).trans hxy⟩

end FsFltz.Geometry.WitnessedPair

namespace FsFltz.Geometry.IntrinsicLiouville

set_option backward.isDefEq.respectTransparency false

/-- Transport a native ribbon presentation along a literal dimension
identity while retaining the native source atlas. -/
theorem native_ribbon_presentation_dimension_eq
    {k d r : ℕ} [NeZero r] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    (hdim : k + 1 = r) (N : SmoothManifold d) (α : Form k M 1)
    (j : M → N.Point) (η : N.Form 1)
    (h : ∃ (F : LiouvilleDomain (k + 1)) (i : M → F.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M F.domain.Point ∞)
      (q : F.domain.extension.SmoothEmbedding N),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = F.domain.carrier ∧ (∀ x, q.map (i x) = j x) ∧
      (∀ x, (F.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x) ∧
      ∀ x ∈ F.domain.carrier, F.domain.extension.pullback N q.map η x =
        F.liouville.primitive x) :
    ∃ (F : LiouvilleDomain r) (i : M → F.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ r) M F.domain.Point ∞)
      (q : F.domain.extension.SmoothEmbedding N),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) ∞ i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x)) ∧
      range i = F.domain.carrier ∧ (∀ x, q.map (i x) = j x) ∧
      (∀ x, (F.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x) = α x) ∧
      ∀ x ∈ F.domain.carrier, F.domain.extension.pullback N q.map η x =
        F.liouville.primitive x := by
  subst r
  exact h

variable {k n : ℕ} [NeZero (2 * n - 2)] {M : Type}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Native positive-dimensional ribbon data produce an actual witnessed
pair on a supplied ambient boundary. The dimension identity is explicit;
both collars and completions are constructed, and the full compact native
ribbon, its embedding and positive witness are retained. -/
theorem exists_native_witnessedPair
    (hdim : k + 1 = 2 * n - 2)
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
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (D : LiouvilleDomain (2 * n)) (j : M → D.domain.boundary.Point)
    (hjs : IsLocallyExtendibleMap (k := k) (F := Model (2 * n - 1)) j)
    (hjinj : Function.Injective j)
    (hjimm : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) j x))
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x)
    (hribbon : ∀ x,
      ((b (j x) • D.domain.boundaryForm D.liouville.primitive (j x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) j x) = α x) :
    ∃ (F : LiouvilleDomain (2 * n - 2)) (i : M → F.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M F.domain.Point ∞)
      (q : F.domain.extension.SmoothEmbedding D.domain.boundary),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x)) ∧
      range i = F.domain.carrier ∧ (∀ x, q.map (i x) = j x) ∧
      (∀ x, (F.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x) = α x) ∧
      ∃ hprimitive : ∀ x ∈ F.domain.carrier,
        F.domain.extension.pullback D.domain.boundary q.map
          (fun y => b y • D.domain.boundaryForm D.liouville.primitive y) x =
          F.liouville.primitive x,
      ∃ (A : LiouvilleDomain.FlowCollar D) (B : LiouvilleDomain.FlowCollar F),
      let P := localizedWitnessedPair D F A B q b hb hpositive hprimitive
      ∃ eP : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞,
        (∀ x, (eP x).val.val.val = i x) ∧
        (∀ x, P.ribbonEmbedding.map (eP x).val = j x) ∧
        P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = range j ∧
        P.witness = b ∧
        (∀ x, (P.ribbonDomain.liouville.primitive (eP x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eP y).val) x) = α x) ∧
        P.embeddedCore = j '' {x | ∀ t : ℝ, 0 ≤ t →
          P.ribbonCompletion.ambient.completeFlow.flow t (P.ribbonCompletion.inclusion.map (eP x).val) ∈
            range (fun y => P.ribbonCompletion.inclusion.map (eP y).val)} := by
  let η : D.domain.boundary.Form 1 := fun y => b y • D.domain.boundaryForm D.liouville.primitive y
  have hpresentation : ∃ (F : LiouvilleDomain (2 * n - 2)) (i : M → F.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M F.domain.Point ∞)
      (q : F.domain.extension.SmoothEmbedding D.domain.boundary),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x)) ∧
      range i = F.domain.carrier ∧ (∀ x, q.map (i x) = j x) ∧
      (∀ x, (F.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x) = α x) ∧
      ∀ x ∈ F.domain.carrier, F.domain.extension.pullback D.domain.boundary q.map η x =
        F.liouville.primitive x := by
    exact native_ribbon_presentation_dimension_eq hdim D.domain.boundary α j η
      (exists_liouvilleDomain_with_native_ribbon_embedding α hα hnd hout
        D.domain.boundary j hjs hjinj hjimm η hribbon)
  obtain ⟨F, i, e, q, he, hi, hdi, hrange, hqj, hpull, hprimitive⟩ := hpresentation
  let A := D.flowCollar
  let B := F.flowCollar
  let P := localizedWitnessedPair D F A B q b hb hpositive hprimitive
  let eP : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞ :=
    e.trans B.originalPointDiffeomorph.symm
  have heP (x : M) : (eP x).val.val.val = i x := he x
  have hjP (x : M) : P.ribbonEmbedding.map (eP x).val = j x := by
    change q.map (eP x).val.val.val = j x
    rw [heP]
    exact hqj x
  refine ⟨F, i, e, q, he, hi, hdi, hrange, hqj, hpull, hprimitive, A, B, eP, heP, hjP, ?_,
    rfl, P.native_ribbon_primitive eP α j hjP ?_, P.embeddedCore_eq_native_image eP.toEquiv j hjP⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx⟩ := eP.surjective ⟨z, hz⟩
      exact ⟨x, (hjP x).symm.trans (congrArg (fun w => P.ribbonEmbedding.map w.val) hx)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(eP x).val, (eP x).property, hjP x⟩
  · change ∀ x, (b (j x) • A.localizedDomain.domain.boundaryForm
      A.localizedDomain.liouville.primitive (j x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) j x) = α x
    rw [A.localized_boundaryForm]
    exact hribbon

end FsFltz.Geometry.IntrinsicLiouville
