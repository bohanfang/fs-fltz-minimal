import FsFltz.Geometry.CommonEmbeddingCompactMap
import FsFltz.Geometry.SmoothIntegralCurveRightUniqueness
import FsFltz.Geometry.TailoringRoundedCompletionMarking
import FsFltz.Geometry.PairFamilyConstruction
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyFields
import FsFltz.Geometry.TailoringHittingPrimitive

/-!
# A finite native hitting trajectory in the actual outer completion

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1905.
Only the native equation on a finite trajectory in the compact carrier is
used. A smooth inverse of the actual native embedding lifts that trajectory;
uniqueness identifies its lift with the chosen completion's actual flow.
No completeness of the native ambient vector field is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold

/-- A native integral curve that stays in a compact region on which the
actual embedding transports the field lifts to the specified complete flow.
Neither the native field nor its equation outside that region is used. -/
theorem CompleteLiouvilleManifold.flow_native_curve_on_finite_interval {d : ℕ}
    (X : CompleteLiouvilleManifold d) (M : SmoothManifold d)
    (e : X.manifold.SmoothEmbedding M) (K : Set X.manifold.Point)
    (Z : (y : M.Point) → M.Tangent y)
    (hfield : ∀ x ∈ K, mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e.map x
      (X.field x) = Z (e.map x))
    {T : ℝ} (hT : 0 < T) (γ : ℝ → M.Point)
    (hγ : IsMIntegralCurveOn γ Z (Icc 0 T))
    (hstay : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ e.map '' K)
    (x : X.manifold.Point) (hzero : γ 0 = e.map x) :
    ∀ t ∈ Icc (0 : ℝ) T,
      X.completeFlow.flow t x ∈ K ∧ e.map (X.completeFlow.flow t x) = γ t := by
  let : Nonempty X.manifold.Point := ⟨x⟩
  let g := Function.invFun e.map
  let ξ : ℝ → X.manifold.Point := g ∘ γ
  have hleft : g ∘ e.map = id :=
    funext (Function.leftInverse_invFun e.embedding.injective)
  have hg (y : M.Point) (hy : y ∈ range e.map) :
      MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g y :=
    ((e.contMDiffOn_invFun.contMDiffAt
      (e.isLocalDiffeomorph.image.isOpen.mem_nhds hy)).mdifferentiableAt (by simp))
  have hξmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ξ t ∈ K := by
    obtain ⟨z, hz, he⟩ := hstay t ht
    change g (γ t) ∈ K
    rw [← he]
    change (g ∘ e.map) z ∈ K
    rw [hleft]
    exact hz
  have heξ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : e.map (ξ t) = γ t :=
    Function.invFun_eq ((hstay t ht).imp (fun z hz => hz.2))
  have hginv (z : X.manifold.Point) (v : X.manifold.Tangent z) :
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g (e.map z)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e.map z v) = v := by
    have hc := mfderiv_comp z (hg _ (mem_range_self z))
      (e.map.contMDiff.mdifferentiableAt (by simp))
    rw [hleft, mfderiv_id] at hc
    exact (congrArg (fun L => L v) hc).symm
  have hξ : IsMIntegralCurveOn ξ X.field (Icc 0 T) := by
    intro t ht
    have hh := (hg _ ((hstay t ht).imp (fun z hz => hz.2))).hasMFDerivAt
      |>.comp_hasMFDerivWithinAt t (hγ t ht)
    apply hh.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) g (γ t)
      (r • Z (γ t)) = r • X.field (ξ t)
    rw [map_smul]
    apply congrArg (fun v => r • v)
    rw [← heξ t ht, ← hfield _ (hξmem t ht)]
    exact hginv _ _
  have hξzero : ξ 0 = x := by
    change g (γ 0) = x
    rw [hzero]
    exact congrFun hleft x
  have hhalf : EqOn ξ (fun t => X.completeFlow.flow t x) (Ico 0 T) :=
    X.manifold.eqOn_of_isMIntegralCurveOn_Ico X.smooth_field
      (hξ.mono Ico_subset_Icc_self)
      ((X.completeFlow.isMIntegralCurve x).isMIntegralCurveOn (Ico 0 T))
      (by simpa only [Flow.map_zero_apply] using hξzero)
  have heq : EqOn ξ (fun t => X.completeFlow.flow t x) (Icc 0 T) :=
    hhalf.of_subset_closure hξ.continuousOn
      (X.completeFlow.contMDiff_orbit x).continuous.continuousOn Ico_subset_Icc_self
      (by rw [closure_Ico hT.ne])
  intro t ht
  have heqt : ξ t = X.completeFlow.flow t x := heq ht
  constructor
  · rw [← heqt]
    exact hξmem t ht
  · rw [← heqt]
    exact heξ t ht

namespace LiouvilleDomain.FlowCollar

/-- On a finite native trajectory in the original compact domain, the
chosen cylindrical completion follows precisely that trajectory under its
actual native projection. Localization does not replace any compact point. -/
theorem native_curve_eq_completed_flow {d : ℕ} {D : LiouvilleDomain d}
    (A : D.FlowCollar) (M : SmoothManifold d)
    (e : D.domain.extension.SmoothEmbedding M)
    (Z : (y : M.Point) → M.Tangent y)
    (hfield : ∀ x ∈ D.domain.carrier,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e.map x (D.liouville.field x) = Z (e.map x))
    {T : ℝ} (hT : 0 < T) (γ : ℝ → M.Point)
    (hγ : IsMIntegralCurveOn γ Z (Icc 0 T))
    (hstay : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ e.map '' D.domain.carrier)
    (x : A.localizedDomain.domain.extension.Point)
    (hzero : γ 0 = e.map (A.originalInclusion.map x)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      A.cylindricalCompletion.ambient.completeFlow.flow t x ∈ A.localizedDomain.domain.carrier ∧
      (e.comp A.originalInclusion).map
        (A.cylindricalCompletion.ambient.completeFlow.flow t x) = γ t := by
  let X := A.cylindricalCompletion.ambient
  let j : X.manifold.SmoothEmbedding M := e.comp A.originalInclusion
  have hjfield : ∀ z ∈ A.localizedDomain.domain.carrier,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j.map z (X.field z) = Z (j.map z) := by
    intro z hz
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (e.map ∘ A.originalInclusion.map) z (X.field z) = _
    rw [mfderiv_comp z (e.map.contMDiff.mdifferentiableAt (by simp))
      (A.originalInclusion.map.contMDiff.mdifferentiableAt (by simp)),
      A.mfderiv_originalInclusion]
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e.map (A.originalInclusion.map z)
      (A.cylindricalCompletion.ambient.field z) = Z (e.map (A.originalInclusion.map z))
    rw [A.cylindricalCompletion_original_field z hz]
    exact hfield _ hz
  have hjstay : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ j.map '' A.localizedDomain.domain.carrier := by
    intro t ht
    change γ t ∈ (e.map ∘ A.originalInclusion.map) '' A.localizedDomain.domain.carrier
    rw [image_comp, A.image_originalInclusion_carrier]
    exact hstay t ht
  exact X.flow_native_curve_on_finite_interval M j A.localizedDomain.domain.carrier
    Z hjfield hT γ hγ hjstay x hzero

/-- A literal native boundary hit is the time-zero end point of this same
chosen completion, reached by its actual forward flow at the same time. -/
theorem native_hitting_eq_completed_end {d : ℕ} {D : LiouvilleDomain d}
    (A : D.FlowCollar) (M : SmoothManifold d)
    (e : D.domain.extension.SmoothEmbedding M)
    (Z : (y : M.Point) → M.Tangent y)
    (hfield : ∀ x ∈ D.domain.carrier,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e.map x (D.liouville.field x) = Z (e.map x))
    {T : ℝ} (hT : 0 < T) (γ : ℝ → M.Point)
    (hγ : IsMIntegralCurveOn γ Z (Icc 0 T))
    (hstay : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ e.map '' D.domain.carrier)
    (x : A.localizedDomain.domain.extension.Point)
    (hzero : γ 0 = e.map (A.originalInclusion.map x))
    (b : D.domain.boundary.Point)
    (hhit : γ T = e.map (D.domain.boundaryInclusion.map b)) :
    A.cylindricalCompletion.ambient.completeFlow.flow T x =
      A.cylindricalCompletion.endMap (b, 0) ∧
    x = A.cylindricalCompletion.endMap (b, -T) := by
  have heq := (A.native_curve_eq_completed_flow M e Z hfield hT γ hγ hstay x hzero)
    T ⟨hT.le, le_rfl⟩
  have hend : A.cylindricalCompletion.ambient.completeFlow.flow T x =
      A.cylindricalCompletion.endMap (b, 0) := by
    apply (e.comp A.originalInclusion).embedding.injective
    rw [heq.2, hhit, A.cylindricalCompletion.end_flow, Flow.map_zero_apply]
    rfl
  refine ⟨hend, ?_⟩
  have h := congrArg (A.cylindricalCompletion.ambient.completeFlow.flow (-T)) hend
  rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply,
    A.cylindricalCompletion.end_flow, Flow.map_zero_apply,
    ← A.cylindricalCompletion.end_flow b (-T)] at h
  exact h

/-- Actual native primitive pullback supplies the carrier field square of
the finite hitting lift. The native ambient need not carry a complete flow. -/
theorem native_hitting_eq_completed_end_of_primitive {d : ℕ} {D : LiouvilleDomain d}
    (A : D.FlowCollar) (M : SmoothManifold d)
    (e : D.domain.extension.SmoothEmbedding M)
    (α : M.Form 1) (hα : M.IsSmoothForm α)
    (hprimitive : D.liouville.primitive = D.domain.extension.pullback M e.map α)
    (hnd : ∀ y ∈ e.map '' D.domain.carrier, M.Nondegenerate (M.exteriorDerivative α) y)
    {T : ℝ} (hT : 0 < T) (γ : ℝ → M.Point)
    (hγ : IsMIntegralCurveOn γ (M.liouvilleVector α) (Icc 0 T))
    (hstay : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ e.map '' D.domain.carrier)
    (x : A.localizedDomain.domain.extension.Point)
    (hzero : γ 0 = e.map (A.originalInclusion.map x))
    (b : D.domain.boundary.Point)
    (hhit : γ T = e.map (D.domain.boundaryInclusion.map b)) :
    A.cylindricalCompletion.ambient.completeFlow.flow T x =
      A.cylindricalCompletion.endMap (b, 0) ∧
    x = A.cylindricalCompletion.endMap (b, -T) := by
  have hfield : ∀ z ∈ D.domain.carrier,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e.map z (D.liouville.field z) =
        M.liouvilleVector α (e.map z) := by
    intro z hz
    rw [D.liouville.field_eq_liouvilleVector z hz]
    exact D.domain.extension.map_liouvilleVector_of_primitive_pullback M rfl e.map
      e.map.contMDiff D.liouville.primitive α hα hprimitive.symm z
      (D.liouville.symplectic.2.2 z hz) (hnd _ (mem_image_of_mem e.map hz))
  exact A.native_hitting_eq_completed_end M e (M.liouvilleVector α) hfield hT γ hγ hstay
    x hzero b hhit

/-- A regional cutoff action's literal outer hit lies on the same escaping
trajectory in the actual chosen completion. Outwardness at every level
crossing proves all pre-hit containment, rather than assuming that bridge. -/
theorem regional_cutoff_hitting_eq_completed_end {d : ℕ} {D : LiouvilleDomain d}
    (C : D.FlowCollar) (M : SmoothManifold d)
    (e : D.domain.extension.SmoothEmbedding M)
    (α : M.Form 1) (hα : M.IsSmoothForm α)
    (hprimitive : D.liouville.primitive = D.domain.extension.pullback M e.map α)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ) (A k : ℝ)
    (himage : e.map '' D.domain.carrier = {y | ρ y ≤ A})
    (hnd : ∀ y, ρ y ≤ A → M.Nondegenerate (M.exteriorDerivative α) y)
    (G : Flow ℝ (ℝ × M.Point))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × (ℝ × M.Point) => G p.1 p.2))
    (hnative : ∀ y t, ρ (G t (k, y)).2 ≤ A →
      IsMIntegralCurveAt (fun s => (G s (k, y)).2) (M.liouvilleVector α) t)
    (hout : ∀ y, ρ y = A → 0 < M.scalarDerivative ρ y (M.liouvilleVector α y))
    {T : ℝ} (hT : 0 < T) (x : C.localizedDomain.domain.extension.Point)
    (b : D.domain.boundary.Point) (hboundary : ρ (e.map (D.domain.boundaryInclusion.map b)) = A)
    (hhit : (G T (k, e.map (C.originalInclusion.map x))).2 =
      e.map (D.domain.boundaryInclusion.map b)) :
    C.cylindricalCompletion.ambient.completeFlow.flow T x =
      C.cylindricalCompletion.endMap (b, 0) ∧
    x = C.cylindricalCompletion.endMap (b, -T) := by
  let γ : ℝ → M.Point := fun t => (G t (k, e.map (C.originalInclusion.map x))).2
  have hlevel : ρ (γ T) = A := (congrArg ρ hhit).trans hboundary
  let f : ℝ → ℝ := ρ ∘ γ
  have hf : Differentiable ℝ f :=
    (hρ.comp (hG.comp (contMDiff_id.prodMk contMDiff_const)).snd).contDiff.differentiable
      (by simp)
  have hpos : ∀ t, f t = A → 0 < deriv f t := by
    intro t ht
    have hd := hasDerivAt_scalar_of_isMIntegralCurveAt M hρ
      (hnative _ t ht.le)
    change 0 < deriv (fun s => ρ (G s (k, e.map (C.originalInclusion.map x))).2) t
    rw [hd.deriv]
    exact hout _ ht
  have hbelow : ∀ t < T, ρ (γ t) < A := by
    intro t ht
    by_contra hn
    have hp := BoundaryOutwardAbsorptionMarking.level_lt_of_boundary_deriv_pos
      (fun s => (hf s).hasDerivAt) hpos (le_of_not_gt hn) ht
    exact (not_lt_of_ge hlevel.le) hp
  have hstay : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ e.map '' D.domain.carrier := by
    intro t ht
    rw [himage]
    rcases ht.2.eq_or_lt with rfl | hlt
    · exact hlevel.le
    · exact (hbelow t hlt).le
  have hγ : IsMIntegralCurveOn γ (M.liouvilleVector α) (Icc 0 T) := by
    intro t ht
    have hmem := hstay t ht
    rw [himage] at hmem
    exact (hnative _ t hmem).hasMFDerivAt.hasMFDerivWithinAt
  apply C.native_hitting_eq_completed_end_of_primitive M e α hα hprimitive
    (fun y hy => hnd y (by rwa [himage] at hy)) hT γ hγ hstay x
      (congrArg Prod.snd (G.map_zero_apply _)) b hhit

end LiouvilleDomain.FlowCollar

end FsFltz.Geometry
