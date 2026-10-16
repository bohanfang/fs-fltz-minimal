import FsFltz.Geometry.TailoringRoundedDomain
import FsFltz.Geometry.FamilyCompletionAssembly

/-!
# Actual negative absorption in the completed finite outer domain

Source: `geometric-part-fsf-proof.tex`, marked-deformation subsection,
lines 1279–1303. Compact confinement and the actual rounded defining-function
derivative force finite entry. The outer completion is the constructed native
cylindrical completion; no completion marking is an input or a conclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

/-- Negative flow preserves the compact piece of every actual completion.
An exterior end point flowed forward remains exterior, so it cannot reach
the compact piece from which the negative orbit began. -/
theorem Completion.flow_neg_mem_compact_image {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) {x : C.ambient.manifold.Point}
    (hx : x ∈ C.inclusion.map '' D.domain.carrier) {t : ℝ} (ht : t ≤ 0) :
    C.ambient.completeFlow.flow t x ∈ C.inclusion.map '' D.domain.carrier := by
  by_contra hnot
  have hc : C.ambient.completeFlow.flow t x ∈
      C.inclusion.map '' D.domain.carrier ∪ C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
    rw [C.covering]
    exact mem_univ _
  obtain ⟨⟨b, r⟩, hr, he⟩ := hc.resolve_left hnot
  have hrpos : 0 < r := by
    rcases lt_or_eq_of_le (show 0 ≤ r from hr.2) with hr | hr
    · exact hr
    · subst r
      apply False.elim (hnot ?_)
      rw [← he, C.endMap_zero]
      exact ⟨D.domain.boundaryInclusion.map b,
        D.domain.compact.isClosed.frontier_subset (D.domain.boundaryInclusion_mem_frontier b), rfl⟩
  have hex : x = C.endMap (b, -t + r) := by
    calc
      x = C.ambient.completeFlow.flow (-t) (C.ambient.completeFlow.flow t x) := by
        rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
      _ = C.ambient.completeFlow.flow (-t) (C.endMap (b, r)) := congrArg _ he.symm
      _ = C.endMap (b, -t + r) := C.flow_endMap b r (-t)
  exact C.overlap b (-t + r) (by linarith) (hex ▸ hx)

/-- Every point of an actual completion enters its compact piece in finite
negative time, directly from the end covering. -/
theorem Completion.exists_nonneg_time_mem_compact_image {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (x : C.ambient.manifold.Point) :
    ∃ T : ℝ, 0 ≤ T ∧
      C.ambient.completeFlow.flow (-T) x ∈ C.inclusion.map '' D.domain.carrier := by
  have hc : x ∈ C.inclusion.map '' D.domain.carrier ∪
      C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
    rw [C.covering]
    exact mem_univ _
  rcases hc with hx | hx
  · exact ⟨0, le_rfl, by simpa using hx⟩
  · obtain ⟨⟨b, r⟩, hr, rfl⟩ := hx
    refine ⟨r, hr.2, ?_⟩
    rw [C.flow_endMap, neg_add_cancel, C.endMap_zero]
    exact ⟨D.domain.boundaryInclusion.map b,
      D.domain.compact.isClosed.frontier_subset (D.domain.boundaryInclusion_mem_frontier b), rfl⟩

/-- A positive scalar derivative on the exterior inside a compact invariant
region forces finite negative entry. Compactness is required only on that
region, rather than on every scalar sublevel in the ambient manifold. -/
theorem exists_nonneg_time_flow_scalar_le_of_compact_confinement
    {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (ρ q : X → ℝ)
    (hρ : Continuous ρ) (hq : Continuous q) {C : Set X} (hcompact : IsCompact C)
    (hderiv : ∀ x t, HasDerivAt (fun s => ρ (F s x)) (q (F t x)) t)
    (hconfine : ∀ x ∈ C, ∀ t : ℝ, t ≤ 0 → F t x ∈ C)
    (A : ℝ) (hpos : ∀ x ∈ C, A ≤ ρ x → 0 < q x) {x : X} (hx : x ∈ C) :
    ∃ T : ℝ, 0 ≤ T ∧ ρ (F (-T) x) ≤ A := by
  by_contra habsorb
  have hout : ∀ t : ℝ, t ≤ 0 → A < ρ (F t x) := by
    intro t ht
    have hn : ¬ ρ (F (-(-t)) x) ≤ A := by
      intro h
      exact habsorb ⟨-t, neg_nonneg.mpr ht, h⟩
    simpa only [neg_neg] using lt_of_not_ge hn
  let f : ℝ → ℝ := fun t => ρ (F t x)
  have hf : Differentiable ℝ f := fun t => (hderiv x t).differentiableAt
  let band : Set X := C ∩ {y | A ≤ ρ y}
  have hband : IsCompact band := hcompact.inter_right (isClosed_le continuous_const hρ)
  have hxband : x ∈ band := by
    refine ⟨hx, ?_⟩
    change A ≤ ρ x
    simpa only [Flow.map_zero_apply] using (hout 0 le_rfl).le
  obtain ⟨y, hy, hmin⟩ := hband.exists_isMinOn ⟨x, hxband⟩ hq.continuousOn
  have hc : 0 < q y := hpos y hy.1 hy.2
  have hbound : ∀ t ∈ interior (Iic (0 : ℝ)), q y ≤ deriv f t := by
    intro t ht
    have ht0 := mem_Iic.mp (interior_subset ht)
    rw [(hderiv x t).deriv]
    exact hmin ⟨hconfine x hx t ht0, (hout t ht0).le⟩
  let T : ℝ := (ρ x - A + 1) / q y
  have hT : 0 < T := div_pos (by have hA : A ≤ ρ x := hxband.2; linarith) hc
  have hslope := (convex_Iic (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hf.continuous.continuousOn hf.differentiableOn hbound
    (-T) (by simpa only [mem_Iic] using (neg_neg_of_pos hT).le)
    0 (by simp) (by linarith)
  have hmul : q y * T = ρ x - A + 1 := by
    dsimp only [T]
    exact mul_div_cancel₀ _ (ne_of_gt hc)
  have houtside := hout (-T) (by linarith)
  simp only [f, Flow.map_zero_apply, sub_neg_eq_add, zero_add] at hslope
  rw [hmul] at hslope
  linarith

namespace LiouvilleDomain.FlowCollar

/-- The native derivative of a scalar pulled back by the actual open
inclusions is its original native derivative, on every tangent vector. -/
theorem scalarDerivative_originalInclusion {d : ℕ} {D : LiouvilleDomain d}
    (C : FlowCollar D) (ρ : D.domain.extension.Point → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (z : C.localizedDomain.domain.extension.Point)
    (v : C.localizedDomain.domain.extension.Tangent z) :
    C.localizedDomain.domain.extension.scalarDerivative
      (fun y => ρ (C.originalInclusion.map y)) z v =
      D.domain.extension.scalarDerivative ρ z.val.val v := by
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun y => ρ y.val.val) z v = _
  have h₁ := mfderiv_comp (f := (Subtype.val : C.neighborhood →
      D.neighborhoodDomain.extension.Point)) (g := fun y => ρ y.val) z
    ((hρ.comp contMDiff_subtype_val).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  erw [D.neighborhoodDomain.extension.mfderiv_restrict_val C.neighborhood z] at h₁
  have h₂ := mfderiv_comp (f := (Subtype.val : D.symplecticNeighborhood →
      D.domain.extension.Point)) (g := ρ) z.val (hρ.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  erw [D.domain.extension.mfderiv_restrict_val D.symplecticNeighborhood z.val] at h₂
  erw [h₁]
  change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun y => ρ y.val) z.val) v = _
  erw [h₂]
  rfl

/-- The actual cylindrical completion absorbs every point into a scalar
sublevel in the original compact piece, using only the actual original
field derivative there. Completeness and negative confinement are supplied
by the construction, rather than assumed by the caller. -/
theorem exists_nonneg_time_original_scalar_le {d : ℕ} {D : LiouvilleDomain d}
    (C : FlowCollar D) (ρ : D.domain.extension.Point → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ) (A : ℝ)
    (hpos : ∀ x ∈ D.domain.carrier, A ≤ ρ x →
      0 < D.domain.extension.scalarDerivative ρ x (D.liouville.field x))
    (x : C.cylindricalCompletion.ambient.manifold.Point) :
    ∃ T : ℝ, 0 ≤ T ∧
      C.cylindricalCompletion.ambient.completeFlow.flow (-T) x ∈
        C.localizedDomain.domain.carrier ∧
      ρ (C.originalInclusion.map (C.cylindricalCompletion.ambient.completeFlow.flow (-T) x)) ≤ A := by
  let P := C.cylindricalCompletion.ambient
  let q := fun z : P.manifold.Point => ρ (C.originalInclusion.map z)
  have hq : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ q :=
    hρ.comp C.originalInclusion.map.contMDiff
  have hconfine (z : P.manifold.Point) (hz : z ∈ C.localizedDomain.domain.carrier)
      (t : ℝ) (ht : t ≤ 0) : P.completeFlow.flow t z ∈ C.localizedDomain.domain.carrier := by
    have h := C.cylindricalCompletion.flow_neg_mem_compact_image
      (show z ∈ C.cylindricalCompletion.inclusion.map '' C.localizedDomain.domain.carrier
        from ⟨z, hz, rfl⟩) ht
    obtain ⟨w, hw, he⟩ := h
    exact he ▸ hw
  have hp (z : P.manifold.Point) (hz : z ∈ C.localizedDomain.domain.carrier) (ha : A ≤ q z) :
      0 < P.manifold.scalarDerivative q z (P.field z) := by
    change 0 < C.localizedDomain.domain.extension.scalarDerivative
      (fun y => ρ (C.originalInclusion.map y)) z (P.field z)
    rw [C.scalarDerivative_originalInclusion ρ hρ]
    erw [C.cylindricalCompletion_original_field z hz]
    exact hpos z.val.val hz ha
  obtain ⟨T₀, hT₀, hentry⟩ := C.cylindricalCompletion.exists_nonneg_time_mem_compact_image x
  have he : P.completeFlow.flow (-T₀) x ∈ C.localizedDomain.domain.carrier := by
    obtain ⟨w, hw, he⟩ := hentry
    exact he ▸ hw
  obtain ⟨T₁, hT₁, hinner⟩ := exists_nonneg_time_flow_scalar_le_of_compact_confinement
    P.completeFlow.flow q (fun z => P.manifold.scalarDerivative q z (P.field z))
    hq.continuous (SmoothManifold.continuous_scalarDerivative_vectorField P.smooth_field q hq)
    C.localizedDomain.domain.compact (P.completeFlow.hasDerivAt_scalar_orbit q hq)
    hconfine A hp he
  refine ⟨T₀ + T₁, add_nonneg hT₀ hT₁, ?_⟩
  rw [show -(T₀ + T₁) = -T₁ + -T₀ by ring, Flow.map_add]
  exact ⟨hconfine _ he (-T₁) (neg_nonpos.mpr hT₁), hinner⟩

end LiouvilleDomain.FlowCollar

end FsFltz.Geometry

namespace FsFltz
open Geometry
variable {n : ℕ}
local instance roundedAbsorptionLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- The literal outer potential domain with the actual tailoring primitive.
Its proof arguments are supplied by the finite-input producer below. -/
def tailoringPotentialOuterDomain (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (β s K A : ℝ)
    (hcompact : IsCompact {y : LGSpace n | φ y.1 - A ≤ 0})
    (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
    (hout : ∀ y : (lgManifold n).Point, φ y.1 - A = 0 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - A) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y)) : LiouvilleDomain (2 * n) :=
  regularSublevelLiouvilleDomain (lgManifold n) (fun y => φ y.1 - A)
    ((contMDiff_potentialValue hφ).sub contMDiff_const) hcompact
    ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)
    ((lgManifold n).isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ)
      (contMDiff_tailoringFamily_lgManifold I β s) K) hω hout

/-- The actual completed outer potential domain absorbs every point into
the literal rounded domain. One coefficient and width work simultaneously
for all tailoring parameters. The completion is constructed from the
produced outer Liouville domain, with any of its native flow collars. -/
theorem tailoringFamily_exists_uniform_rounded_absorption
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ K ≥ Kstar, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∃ (hcompact : IsCompact {y : LGSpace n | φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0})
        (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
        (hout : ∀ y : (lgManifold n).Point, φ y.1 - D ^ 2 * β ^ 2 / 2 = 0 →
          0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - D ^ 2 * β ^ 2 / 2) y
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β s) K) y)),
      let E := tailoringPotentialOuterDomain I hφ β s K (D ^ 2 * β ^ 2 / 2) hcompact hω hout
      E.domain.carrier.Nonempty ∧ ∀ C : LiouvilleDomain.FlowCollar E,
      ∀ z : C.cylindricalCompletion.ambient.manifold.Point,
      ∃ T : ℝ, 0 ≤ T ∧
        C.cylindricalCompletion.ambient.completeFlow.flow (-T) z ∈ C.localizedDomain.domain.carrier ∧
        (C.cylindricalCompletion.ambient.completeFlow.flow (-T) z).val.val ∈
          tailoringRoundedDomain I φ β s R (D ^ 2 * β ^ 2 / 2) m := by
  obtain ⟨Bo, _hBo, ho⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  obtain ⟨BD, _hBD, hDdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  let β₀ := max 1 (max Bo BD)
  refine ⟨β₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβo : Bo ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβD : BD ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hcompact, hnonempty, hdata⟩ := hDdata β hβD
  obtain ⟨Kstar, hKstar, hout⟩ := ho β hβo
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout R hR Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd K hK s hs
  obtain ⟨hω, hb⟩ := hdata s hs K (hKstar.le.trans hK)
  refine ⟨hcompact, hω, hb, hnonempty, ?_⟩
  intro C z
  let q := tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m
  have hp : ∀ y ∈ (tailoringPotentialOuterDomain I hφ β s K
      (D ^ 2 * β ^ 2 / 2) hcompact hω hb).domain.carrier, 0 ≤ q y →
      0 < (lgManifold n).scalarDerivative q y ((lgManifold n).liouvilleVector
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K) y) := by
    intro y hy hq
    exact hout m hm hmd K hK s hs y (sub_nonpos.mp hy) hq
  exact C.exists_nonneg_time_original_scalar_le q
    (contMDiff_tailoringRoundedDefiningFunction I hφ β s R (D ^ 2 * β ^ 2 / 2) m)
    0 hp z

end FsFltz
