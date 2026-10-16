import FsFltz.Geometry.TailoringNormalCoordinates
import FsFltz.Analysis.CoordinateStrongConvexLegendre

/-!
# A common transverse zero set for the actual conormal branch

Source: `geometric-part-fsf-proof.tex`, `lem:stable`, lines 1709–1724.
The quotient-defined transverse map is joined to the constructed embedded
conormal branch on one open neighborhood containing the entire face torus.
The positive-coefficient face condition supplies the required relative
interior neighborhood; membership in the span is consequently actual
membership in the positive cone here. This constructs a common defining
neighborhood, not a product tubular chart or a trapping estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function TopologicalSpace
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- On the actual endpoint fiber, the literal cutoff plateau removes all
nonface terms. No small-monomial cutoff is suppressed as an assumption. -/
theorem tailoringFamily_face_sum_of_point_plateau
    (I : ToricInput n) (β : ℝ) {s : Finset (Lattice n)} (hsub : s ⊆ I.vertices)
    (w : LGSpace n) (hw : tailoringFamily I β 1 w = 1)
    (hcut : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v w.1 = if v = 0 ∨ v ∈ s then 1 else 0) :
    ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v w = 1 := by
  classical
  have hz : tailoringCutoff I β 0 w.1 = 1 := by
    simpa using hcut 0 (Finset.mem_insert_self _ _)
  have hsum := sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β w hw
  rw [hz, Complex.ofReal_one] at hsum
  calc
    _ = ∑ v ∈ s, tailoringRetainedMonomial I β v w := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [tailoringRetainedMonomial, hcut v (Finset.mem_insert_of_mem (hsub hv)), hv]
    _ = ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v w := by
      apply Finset.sum_subset hsub
      intro v hv hvs
      have hv0 : v ≠ 0 := fun he => I.zero_not_mem_vertices (he ▸ hv)
      simp [tailoringRetainedMonomial, hcut v (Finset.mem_insert_of_mem hv), hv0, hvs]
    _ = 1 := hsum

/-- The branch, quotient projection and common open neighborhood are all
constructed. The analytical plateau is the literal cutoff equality, and
the strictly positive face coefficients are the actual critical-point
data, rather than an assumed chart or assumed normal vector field. -/
theorem IsStronglyCompatibleEndPotential.eventually_exists_conormalTransverseNeighborhood
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φ u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n))) :
    ∀ᶠ β in atTop, ∀ s : Finset (Lattice n),
      IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∀ y : LGSpace n, y.2 ∈ coneTorus (positiveCone s) →
      tailoringFamily I β 1 y = 1 →
      ∀ a : s → ℝ, (∀ v, 0 < a v) → Φ y.1 = faceNormalMap s a →
      ∀ ℓ : RealSpace n →L[ℝ] ℝ, ℓ (Φ y.1) = 1 →
      ∀ U : Set (RealSpace n), IsOpen U → y.1 ∈ U →
      (∀ u ∈ U, ∀ v ∈ tailoringExponents I,
        tailoringCutoff I β v u = if v = 0 ∨ v ∈ s then 1 else 0) →
      ∀ v₀ : s,
      ∃ (P : RealSpace n →L[ℝ] Submodule.span ℝ (positiveCone s))
        (Q : RealSpace n →L[ℝ] P.ker)
        (B : Opens (conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ))
        (g : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ → RealSpace n)
        (f : Torus (n - s.card) → Torus n) (O : Set (LGSpace n)),
        LeftInverse P (Submodule.span ℝ (positiveCone s)).subtypeL ∧
        Surjective Q ∧ (∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s)) ∧
        (0 : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ) ∈ B ∧
        g 0 = y.1 ∧ range f = coneTorus (positiveCone s) ∧
        Topology.IsEmbedding (Prod.map (fun q : B => g q) f) ∧
        (∀ q ∈ B, ∀ θ : Torus (n - s.card),
          ContMDiffAt ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
            (torusModel (n - s.card))) (lgModel n) ∞ (Prod.map g f) (q, θ) ∧
          Injective (mfderiv
            ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
              (torusModel (n - s.card))) (lgModel n) (Prod.map g f) (q, θ))) ∧ IsOpen O ∧
        (∀ θ ∈ coneTorus (positiveCone s),
          (y.1, θ) ∈ O ∧ tailoringFamily I β 1 (y.1, θ) = 1 ∧
          conormalTransverseCoordinates Φ Q s v₀.val (y.1, θ) = 0) ∧
        (∀ w ∈ O, ContMDiffAt (lgModel n)
          𝓘(ℝ, P.ker × (s.erase v₀.val → ℝ)) ∞
          (conormalTransverseCoordinates Φ Q s v₀.val) w) ∧
        (∀ w ∈ O, tailoringFamily I β 1 w = 1 →
          (conormalTransverseCoordinates Φ Q s v₀.val w = 0 ↔
            w ∈ range (Prod.map (fun q : B => g q) f))) ∧
        (∀ w ∈ O, tailoringFamily I β 1 w = 1 →
          (conormalTransverseCoordinates Φ Q s v₀.val w = 0 ↔
            Φ w.1 ∈ positiveCone s ∧ w.2 ∈ coneTorus (positiveCone s))) := by
  classical
  filter_upwards [hφ.eventually_exists_embedded_conormalBranch Φ hΦeq hΦ₀ hΦ hΦinv]
    with β hbranch
  intro s hs hsne hsproper y hθ hy a ha hya ℓ hℓ U hU hyU hcut v₀
  have hp : Φ y.1 ∈ positiveCone s := by
    rw [hya]
    exact faceNormalMap_mem_positiveCone a (fun v => (ha v).le)
  obtain ⟨B, g, f, R, h₀, hg₀, hf, hR, hemb, hDg, hprops, himage⟩ :=
    hbranch s hs hsne hsproper y hp hθ hy ℓ hℓ
  obtain ⟨P, Q, hP, hQsurj, hQ⟩ :=
    exists_surjective_conormalRadialQuotient (Submodule.span ℝ (positiveCone s))
  have hcone : ∀ᶠ u in 𝓝 y.1,
      Φ u ∈ Submodule.span ℝ (positiveCone s) → Φ u ∈ positiveCone s := by
    have hn := I.eventually_span_mem_positiveCone hs hsne hsproper a ha
    rw [← hya] at hn
    exact Φ.continuous.continuousAt.eventually hn
  have hyne : y.1 ≠ 0 := by
    intro he
    rw [he, hΦ₀, map_zero] at hℓ
    exact zero_ne_one hℓ
  have hnear : ∀ᶠ u in 𝓝 y.1,
      u ∈ U ∧ u ≠ 0 ∧
      (Φ u ∈ Submodule.span ℝ (positiveCone s) → Φ u ∈ positiveCone s) ∧
      (∀ θ : Torus n, (u, θ) ∈ range (Prod.map (fun q : B => g q) f) ↔
        tailoringFamily I β 1 (u, θ) = 1 ∧
        Φ u ∈ Submodule.span ℝ (positiveCone s) ∧ θ ∈ coneTorus (positiveCone s)) := by
    filter_upwards [hU.eventually_mem hyU, isOpen_compl_singleton.eventually_mem hyne,
      hcone, himage] with u hu hne hc hi
    exact ⟨hu, hne, hc, hi⟩
  obtain ⟨W, hWsub, hWopen, hyW⟩ := mem_nhds_iff.mp hnear
  let O : Set (LGSpace n) := Prod.fst ⁻¹' W ∩ conormalPositivePhaseNeighborhood s
  have hO : IsOpen O := (hWopen.preimage continuous_fst).inter
    (isOpen_conormalPositivePhaseNeighborhood s)
  have hzero (w : LGSpace n) (hw : w ∈ O) (hlevel : tailoringFamily I β 1 w = 1) :
      conormalTransverseCoordinates Φ Q s v₀.val w = 0 ↔
        Φ w.1 ∈ Submodule.span ℝ (positiveCone s) ∧ w.2 ∈ coneTorus (positiveCone s) := by
    apply conormalTransverseCoordinates_eq_zero_iff I hs hsne hsproper Φ
      (Submodule.span ℝ (positiveCone s)) Q hQ v₀.val v₀.property w hw.2
      (Real.exp (-β)) (Real.exp_pos _)
    exact tailoringFamily_face_sum_of_point_plateau I β hs.1 w hlevel
      (hcut w.1 (hWsub hw.1).1)
  refine ⟨P, Q, B, g, f, O, hP, hQsurj, hQ, h₀, hg₀, hf, hemb,
    (fun q hq θ => ⟨(hprops q hq θ).1, (hprops q hq θ).2.1⟩), hO, ?_, ?_, ?_, ?_⟩
  · intro θ hθ'
    have hwO : (y.1, θ) ∈ O := ⟨hyW,
      mem_conormalPositivePhaseNeighborhood_of_mem_coneTorus I hs hsne hsproper _ hθ'⟩
    obtain ⟨θ', hθ'eq⟩ := hf.symm ▸ hθ'
    have hfiber := (hprops 0 h₀ θ').2.2.1
    change tailoringFamily I β 1 (g 0, f θ') = 1 at hfiber
    rw [hg₀, hθ'eq] at hfiber
    refine ⟨hwO, hfiber, (hzero _ hwO hfiber).mpr ?_⟩
    exact ⟨Submodule.subset_span hp, hθ'⟩
  · intro w hw
    apply contMDiffAt_conormalTransverseCoordinates Q s v₀.val w
    exact hΦ.contDiffAt (isOpen_compl_singleton.mem_nhds (hWsub hw.1).2.1)
  · intro w hw hlevel
    rw [hzero w hw hlevel]
    have hi := (hWsub hw.1).2.2.2 w.2
    change w ∈ range (Prod.map (fun q : B => g q) f) ↔ _ at hi
    simpa only [hlevel, true_and] using hi.symm
  · intro w hw hlevel
    rw [hzero w hw hlevel]
    constructor
    · rintro ⟨hp', hθ'⟩
      exact ⟨(hWsub hw.1).2.2.1 hp', hθ'⟩
    · rintro ⟨hp', hθ'⟩
      exact ⟨Submodule.subset_span hp', hθ'⟩

/-- The actual constrained minimum and normalized reduced branch supply
the common neighborhood. Every geometric object in the conclusion is
constructed; the hypotheses concern only the strongly compatible end
potential and its quantitative convexity. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_face_conormalTransverseNeighborhood
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φ)
    (hφ1 : ContDiff ℝ 1 φ) (hφ0 : φ 0 = 0)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    (hlower : ∀ u : EuclideanSpace ℝ (Fin n),
      c * ‖u‖ ^ 2 ≤ φ ((EuclideanSpace.equiv (Fin n) ℝ) u))
    (hbound : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → ∀ v,
      (2 * c) * ‖v‖ ^ 2 ≤ inner ℝ
        ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u) v) v)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ z : ℝ → ((s → ℝ) × ℝ),
      x 0 ∈ polarFace I s ∧ IsMinOn φ (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ z 0 ∧
      ∀ᶠ β : ℝ in atTop, ∀ v₀ : s,
        ∃ (ℓ : RealSpace n →L[ℝ] ℝ)
          (P : RealSpace n →L[ℝ] Submodule.span ℝ (positiveCone s))
          (Q : RealSpace n →L[ℝ] P.ker)
          (B : Opens (conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ))
          (g : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ → RealSpace n)
          (f : Torus (n - s.card) → Torus n) (O : Set (LGSpace n)),
          ℓ (coordinateGradient φ (faceCriticalRadius x z β)) = 1 ∧
          LeftInverse P (Submodule.span ℝ (positiveCone s)).subtypeL ∧
          Surjective Q ∧ (∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s)) ∧
          (0 : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ) ∈ B ∧
          g 0 = faceCriticalRadius x z β ∧ range f = coneTorus (positiveCone s) ∧
          Topology.IsEmbedding (Prod.map (fun q : B => g q) f) ∧
          (∀ q ∈ B, ∀ θ : Torus (n - s.card),
            ContMDiffAt ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
              (torusModel (n - s.card))) (lgModel n) ∞ (Prod.map g f) (q, θ) ∧
            Injective (mfderiv
              ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
                (torusModel (n - s.card))) (lgModel n) (Prod.map g f) (q, θ))) ∧ IsOpen O ∧
          (∀ θ ∈ coneTorus (positiveCone s),
            (faceCriticalRadius x z β, θ) ∈ O ∧
            tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
            conormalTransverseCoordinates (coordinateGradient φ) Q s v₀.val
              (faceCriticalRadius x z β, θ) = 0) ∧
          (∀ w ∈ O, ContMDiffAt (lgModel n)
            𝓘(ℝ, P.ker × (s.erase v₀.val → ℝ)) ∞
            (conormalTransverseCoordinates (coordinateGradient φ) Q s v₀.val) w) ∧
          (∀ w ∈ O, tailoringFamily I β 1 w = 1 →
            (conormalTransverseCoordinates (coordinateGradient φ) Q s v₀.val w = 0 ↔
              w ∈ range (Prod.map (fun q : B => g q) f))) ∧
          (∀ w ∈ O, tailoringFamily I β 1 w = 1 →
            (conormalTransverseCoordinates (coordinateGradient φ) Q s v₀.val w = 0 ↔
              coordinateGradient φ w.1 ∈ positiveCone s ∧
                w.2 ∈ coneTorus (positiveCone s))) := by
  classical
  have hgrad0 : coordinateGradient φ 0 = 0 := by
    have hm : IsLocalMin φ 0 := Filter.Eventually.of_forall fun u => by
      rw [hφ0]
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (mul_nonneg hc.le (sq_nonneg _)).trans
          (hlower ((EuclideanSpace.equiv (Fin n) ℝ).symm u))
    ext i
    simp [coordinateGradient, hm.fderiv_eq_zero]
  let Φ := strongConvexCoordinateGradientHomeomorph hφ1 hc hconv hlower
  have hΦeq : ∀ u, Φ u = coordinateGradient φ u :=
    fun u => strongConvexCoordinateGradientHomeomorph_apply hφ1 hc hconv hlower u
  have hΦfun : (Φ : RealSpace n → RealSpace n) = coordinateGradient φ := funext hΦeq
  have hΦ₀ : Φ 0 = 0 := by simpa [Φ] using hgrad0
  have hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_strongConvexCoordinateGradientHomeomorph hφ1 hc hconv hlower hStrong.smooth
  have hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_symm_strongConvexCoordinateGradientHomeomorph hφ1 hc hconv hlower hgrad0
      hStrong.smooth (show 0 < 2 * c by positivity) hbound
  obtain ⟨x, z, hx₀, hm₀, hxs, has, hpos, hz₀, hzs, hsol, hzsol, _, hradial, hfiber⟩ :=
    hStrong.exists_actual_positive_faceReduced_branch hφ1 hc hconv hs hsne hsproper
  have hμ : 0 < ∑ v, faceReducedCoefficient φ x 0 v := by
    let : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
    exact Finset.sum_pos (fun v _ => hpos v) Finset.univ_nonempty
  have hq₀ : ∀ v, 0 < (z 0).1 v := by
    intro v
    rw [hz₀]
    exact div_pos (hpos v) hμ
  have hstrict := hStrong.strict_of_polarFace_minimum hs hsne hsproper hx₀ hm₀
  have hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1 := by
    intro v hv
    split_ifs with hvs
    · exact hx₀.2 v hvs
    · exact hstrict v hv hvs
  have hcut := critical_reduced_branch_eventually_face_plateaus I
    (hxs.differentiableAt (by simp)) hface (hzs.fst.differentiableAt (by simp)) hq₀
  refine ⟨x, z, hx₀, hm₀, hxs, hzs, ?_⟩
  filter_upwards [hStrong.eventually_exists_conormalTransverseNeighborhood
      Φ hΦeq hΦ₀ hΦ hΦinv,
    hcut, hradial, hfiber, tendsto_inv_atTop_zero.eventually hzsol,
    eventually_gt_atTop (0 : ℝ)] with β hnb hcutβ hradβ hfiberβ hsolβ hβ
  intro v₀
  let a : s → ℝ := (β * (z β⁻¹).2) • (z β⁻¹).1
  have ha : ∀ v, 0 < a v := fun v =>
    mul_pos (mul_pos hβ hsolβ.2.1) (hsolβ.1 v)
  have hnormal : Φ (faceCriticalRadius x z β) = faceNormalMap s a := by
    rw [hΦeq, hradβ]
    exact (map_smul (faceNormalMap s) _ _).symm
  have hpne : Φ (faceCriticalRadius x z β) ≠ 0 := by
    rw [hnormal]
    intro hz
    have ha0 : a = 0 := (faceNormalMap_injective_of_surjective
      (I.faceLevelMap_surjective hs hsne hsproper)) (hz.trans (map_zero _).symm)
    have := ha v₀
    rw [ha0] at this
    exact lt_irrefl 0 this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hpne
  let ℓ : RealSpace n →L[ℝ] ℝ :=
    (Φ (faceCriticalRadius x z β) i)⁻¹ • ContinuousLinearMap.proj i
  have hℓ : ℓ (Φ (faceCriticalRadius x z β)) = 1 := by
    exact inv_mul_cancel₀ hi
  have hθ0 := zero_mem_coneTorus (positiveCone s)
  have hfiber0 := hfiberβ 0 (fun v =>
    (I.mem_coneTorus_positiveCone_iff hs hsne hsproper 0).mp hθ0 v.val v.property)
  obtain ⟨U, hU, huU, hcutU⟩ := hcutβ
  obtain ⟨P, Q, B, g, f, O, hdata⟩ :=
    hnb s hs hsne hsproper (faceCriticalRadius x z β, 0) hθ0 hfiber0
      a ha hnormal ℓ hℓ U hU huU hcutU v₀
  refine ⟨ℓ, P, Q, B, g, f, O, ?_, ?_⟩
  · rwa [← hΦeq]
  · simpa only [hΦfun] using hdata

end FsFltz
