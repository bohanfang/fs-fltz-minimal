import FsFltz.Geometry.IntrinsicCompletionFlow
import FsFltz.Geometry.IntrinsicCompletionDomain
import FsFltz.Geometry.IntrinsicCompletionLiouville
import FsFltz.Geometry.CylindricalCompletion

/-!
# Completion on the actual intrinsic half-infinite quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160, especially
142–158, and `sec:lean`, lines 783–814. The compact domain and completed
ambient share the actual quotient, so the completion inclusion is identity.
The end map is the all-real complete boundary orbit, with the literal
attached cylinder identified on its signed source by ODE uniqueness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing
open SmoothManifold

variable {k : ℕ} {M : Type} [TopologicalSpace M] [CompactSpace M]
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
  (α : IntrinsicLiouville.Form k M 1)
  (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
  (L : LiouvilleStructure (compactDomain hδ C hemb hC hboundary hinv hzero))
  (hnd : ∀ x, (completionManifold hδ C hemb hC hboundary hinv hzero).Nondegenerate
    ((completionManifold hδ C hemb hC hboundary hinv hzero).exteriorDerivative L.primitive) x)
  (hcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
    (completionManifold hδ C hemb hC hboundary hinv hzero)
    (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) L.primitive =
      cylinderPrimitive δ α)

/-- The complete canonical flow constructed from this very global primitive. -/
def completeFlow : CompleteLiouvilleFlow
    (completionManifold hδ C hemb hC hboundary hinv hzero)
    ((completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleVector L.primitive) :=
  Classical.choice (exists_completeLiouvilleFlow hδ C hemb hC hboundary hinv hzero
    α hα L.primitive L.smooth_primitive hnd hcylinder)

include α hα hnd hcylinder in
/-- The canonical complete flow and the attached cylinder agree wherever
the latter is defined, including the seam and all nonnegative radii. -/
theorem boundaryOrbitMap_eq_outwardEndMap
    (F : CompleteLiouvilleFlow (completionManifold hδ C hemb hC hboundary hinv hzero)
      ((completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleVector L.primitive))
    (p : IntrinsicBoundary.Point k M × ℝ) (hp : -δ < p.2) :
    F.boundaryOrbitMap (compactDomain hδ C hemb hC hboundary hinv hzero) p =
      outwardEndMap hδ C p := by
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let D := compactDomain hδ C hemb hC hboundary hinv hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  apply F.boundaryOrbitMap_eq_of_isMIntegralCurveOn D
    (X.isSmoothVectorField_liouvilleVector L.primitive L.smooth_primitive hnd) hδ
    (outwardEndMap hδ C)
    (isMIntegralCurveOn_outwardEndMap hδ C hemb hC hboundary hinv hzero
      α hα L.primitive L.smooth_primitive hnd hcylinder) ?_ p hp
  intro b
  rw [outwardEndMap_eq_cylinder hδ C (b, 0) (neg_lt_zero.mpr hδ),
    compactDomain_boundaryInclusion_cylinder]
  congr 1
  apply Subtype.ext
  simp

/-- The actual canonical complete ambient on the constructed quotient. -/
def completeAmbient : CompleteLiouvilleManifold (k + 1) where
  manifold := completionManifold hδ C hemb hC hboundary hinv hzero
  primitive := L.primitive
  smooth_primitive := L.smooth_primitive
  symplectic := ((completionManifold hδ C hemb hC hboundary hinv hzero).isSymplecticOn_exteriorDerivative_iff
    L.primitive L.smooth_primitive univ).mpr
      (fun x _ => hnd x)
  field := (completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleVector L.primitive
  smooth_field := (completionManifold hδ C hemb hC hboundary hinv hzero).isSmoothVectorField_liouvilleVector
    L.primitive L.smooth_primitive hnd
  contraction := fun x => (completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleVector_contraction
    L.primitive x ((completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleEquation_exists
      L.primitive x (hnd x))
  completeFlow := completeFlow hδ C hemb hC hboundary hinv hzero α hα L hnd hcylinder

/-- Identity inclusion into the actual quotient, with its all-real orbit
end and the prescribed attached exterior. The input Liouville structure
and cylinder laws will be supplied by the native construction below. -/
def completion : Completion ⟨compactDomain hδ C hemb hC hboundary hinv hzero, L⟩ := by
  let D := compactDomain hδ C hemb hC hboundary hinv hzero
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let F := completeFlow hδ C hemb hC hboundary hinv hzero α hα L hnd hcylinder
  let := completionChartedSpace hδ C hemb hboundary hzero
  have heq (p : IntrinsicBoundary.Point k M × ℝ) (hp : -δ < p.2) :
      F.boundaryOrbitMap D p = cylinder
        (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
        (⟨(-p.2, p.1), neg_lt.mp hp, mem_univ _⟩ : Band δ (IntrinsicBoundary.Point k M)) :=
    (boundaryOrbitMap_eq_outwardEndMap hδ C hemb hC hboundary hinv hzero α hα L hnd hcylinder
      F p hp).trans (outwardEndMap_eq_cylinder hδ C p hp)
  refine {
    ambient := completeAmbient hδ C hemb hC hboundary hinv hzero α hα L hnd hcylinder
    inclusion := {
      map := ContMDiffMap.id
      embedding := IsEmbedding.id
      immersion := fun x => by
        change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) id x)
        rw [mfderiv_id]
        exact Function.injective_id }
    primitive_on_domain := fun x _ => congrFun (X.pullback_id L.primitive) x
    field_on_domain := ?_
    endMap := F.boundaryOrbitMap D
    smooth_endMap := F.smooth_boundaryOrbitMap D
    end_flow := fun _ _ => rfl
    end_embedding := ?_
    end_immersion := ?_
    end_primitive := ?_
    covering := ?_
    overlap := ?_ }
  · intro x hx
    change mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) id x (L.field x) =
      X.liouvilleVector L.primitive x
    rw [mfderiv_id]
    exact L.field_eq_liouvilleVector x hx
  · let i : IntrinsicBoundary.Point k M × Ici (0 : ℝ) → End (IntrinsicBoundary.Point k M) :=
      fun p => ⟨(p.2.val, p.1), p.2.property, mem_univ _⟩
    have hi : IsEmbedding i := (IsEmbedding.subtypeVal.of_comp_iff).mp
      ((Homeomorph.prodComm (IntrinsicBoundary.Point k M) ℝ).isEmbedding.comp
        (IsEmbedding.id.prodMap IsEmbedding.subtypeVal))
    have he : (fun p : IntrinsicBoundary.Point k M × Ici (0 : ℝ) =>
        F.boundaryOrbitMap D (p.1, p.2.val)) =
        endIn hδ (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) ∘ i := by
      funext p
      exact heq (p.1, p.2.val)
        (lt_of_lt_of_le (neg_lt_zero.mpr hδ) (show 0 ≤ p.2.val from p.2.property))
    erw [he]
    exact (isEmbedding_endIn hδ _ hemb).comp hi
  · exact F.boundaryOrbitMap_immersion D L (fun b =>
      (L.field_eq_liouvilleVector _
        (D.compact.isClosed.frontier_subset (D.boundaryInclusion_mem_frontier b))).symm)
  · intro b r v s
    exact F.boundaryOrbitMap_primitive D L.primitive L.smooth_primitive
      (fun x => X.liouvilleVector_contraction L.primitive x
        (X.liouvilleEquation_exists L.primitive x (hnd x))) b r v s
  · change id '' D.carrier ∪ F.boundaryOrbitMap D '' (univ ×ˢ Ici (0 : ℝ)) = univ
    rw [image_id]
    apply Set.eq_univ_of_forall
    intro x
    rcases original_endIn_cover hδ
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x with hx | ⟨p, rfl⟩
    · exact Or.inl (by simpa only [D, compactDomain_carrier] using hx)
    · exact Or.inr ⟨(p.val.2, p.val.1), ⟨mem_univ _, p.property.1⟩,
        heq _ (lt_of_lt_of_le (neg_lt_zero.mpr hδ) (show 0 ≤ p.val.1 from p.property.1))⟩
  · intro b r hr
    change F.boundaryOrbitMap D (b, r) ∉ id '' D.carrier
    dsimp only [D]
    erw [image_id, compactDomain_carrier, heq _ (lt_trans (neg_lt_zero.mpr hδ) hr)]
    rintro ⟨x, hx⟩
    have h := (original_eq_cylinder_iff
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x
      (⟨(-r, b), neg_lt.mp (lt_trans (neg_lt_zero.mpr hδ) hr), mem_univ _⟩ :
        Band δ (IntrinsicBoundary.Point k M))).mp hx
    exact (not_le_of_gt hr) (neg_nonneg.mp h.choose)

@[simp] theorem completion_inclusion (x : (completionManifold hδ C hemb hC hboundary hinv hzero).Point) :
    (completion hδ C hemb hC hboundary hinv hzero α hα L hnd hcylinder).inclusion.map x = x := rfl

/-- The compact quotient boundary form is precisely the restriction of the
original native primitive, using the actual derivative of boundary inclusion. -/
theorem boundaryForm_eq_restrictForm
    (hnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      (fun x => (L.primitive (original
        (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
            (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x)) = α) :
    (compactDomain hδ C hemb hC hboundary hinv hzero).boundaryForm L.primitive =
      IntrinsicBoundary.restrictForm α := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let D := compactDomain hδ C hemb hC hboundary hinv hzero
  let i := original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  have hb : (D.boundaryInclusion.map : IntrinsicBoundary.Point k M → D.extension.Point) =
      i ∘ (Subtype.val : IntrinsicBoundary.Point k M → M) :=
    funext (compactDomain_boundaryInclusion hδ C hemb hC hboundary hinv hzero)
  funext b
  unfold CompactDomain.boundaryForm SmoothManifold.pullback
  rw [hb]
  erw [mfderiv_comp (I := 𝓘(ℝ, Model k)) (I' := 𝓡∂ (k + 1))
    (I'' := 𝓘(ℝ, Model (k + 1)))
    (f := (Subtype.val : IntrinsicBoundary.Point k M → M)) (g := i) b
    ((contMDiff_original hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    (IntrinsicBoundary.contMDiff_val.mdifferentiableAt (by simp))]
  ext vs
  exact congrArg (fun eta => eta (fun n =>
    mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
      (Subtype.val : IntrinsicBoundary.Point k M → M) b (vs n))) (congrFun hnative b.val)

/-- At every real radius the actual completion end has the exponential
primitive of the original native boundary. This includes negative radii
beyond the local collar, where the all-real orbit supplies the end map. -/
theorem completion_original_end_primitive
    (hnative : letI := completionChartedSpace hδ C hemb hboundary hzero
      (fun x => (L.primitive (original
        (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
            (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) x)) = α)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) (v : Model k) (s : ℝ) :
    let Q := completion hδ C hemb hC hboundary hinv hzero α hα L hnd hcylinder
    evalOne Q.ambient.primitive (Q.endMap (b, r))
      (mfderiv (𝓘(ℝ, Model k).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (k + 1))
        Q.endMap (b, r) (v, s)) =
      Real.exp r * evalOne (M := IntrinsicBoundary.smoothManifold k M)
        (IntrinsicBoundary.restrictForm α) b v := by
  have h := (completion hδ C hemb hC hboundary hinv hzero α hα L hnd hcylinder).end_primitive b r v s
  rw [boundaryForm_eq_restrictForm hδ C hemb hC hboundary hinv hzero α L hnative] at h
  exact h

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicLiouville
open IntrinsicCompletionGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- A compact native Liouville manifold constructs its actual completion
from the source primitive and local outwardness alone. The same original
points retain their topology, tangent spaces, full primitive and field in
the completed ambient. The output `Completion` includes all-real smooth
flow, its all-real exponential end law, end immersion and full end coverage. -/
theorem exists_completion_from_native
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
    ∃ (D : LiouvilleDomain (k + 1)) (Q : Completion D) (i : M → D.domain.extension.Point),
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.domain.carrier ∧
      frontier D.domain.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      (∀ x, (D.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x) ∧
      (∀ x, (Q.ambient.primitive (Q.inclusion.map (i x))).compContinuousLinearMap
        ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) Q.inclusion.map (i x)).comp
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α x) ∧
      (∀ x, Q.ambient.field (Q.inclusion.map (i x)) =
        mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) Q.inclusion.map (i x)
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
            (liouvilleVector α (exteriorDerivative α) x))) := by
  obtain ⟨C, δ, hδ, hemb, hC, hboundary, hinv, hzero,
      L, _, hnative, hcylinder, hglobal, hfield, hnativeField, _⟩ :=
    exists_liouvilleStructure_from_native α hα hnd hout
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let D : LiouvilleDomain (k + 1) := ⟨compactDomain hδ C hemb hC hboundary hinv hzero, L⟩
  let Q := completion hδ C hemb hC hboundary hinv hzero α hα L hglobal hcylinder
  let i := original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
  let := completionChartedSpace hδ C hemb hboundary hzero
  refine ⟨D, Q, i,
    contMDiff_original hδ C hemb hC hboundary hinv hzero,
    isClosedEmbedding_original hδ _ hemb,
    bijective_mfderiv_original hδ C hemb hC hboundary hinv hzero,
    (compactDomain_carrier hδ C hemb hC hboundary hinv hzero).symm,
    compactDomain_frontier hδ C hemb hC hboundary hinv hzero,
    congrFun hnative, ?_, ?_⟩
  · intro x
    change (L.primitive (i x)).compContinuousLinearMap
      ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) id (i x)).comp
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α x
    rw [mfderiv_id, ContinuousLinearMap.id_comp]
    exact congrFun hnative x
  · intro x
    change X.liouvilleVector L.primitive (i x) =
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) id (i x)
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
          (liouvilleVector α (exteriorDerivative α) x))
    rw [mfderiv_id]
    exact (congrFun hfield (i x)).symm.trans (hnativeField x)

end FsFltz.Geometry.IntrinsicLiouville
