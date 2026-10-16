import FsFltz.Analysis.TailoringClosedTransition
import FsFltz.Analysis.TailoringFiberCriticalGood

/-!
# Open holomorphic neighborhoods of actual intrinsic critical points

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1428–1434
and 1452–1461. The strict plateau gaps follow from closed-strip separation
and the actual full-fiber critical conormal estimate. Neighborhoods and their
proper nonempty face supports are constructed, rather than supplied as input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- A weight strictly beyond the cutoff strip has an exactly vanishing
cutoff, by the factor corresponding to an attained maximal exponent. -/
theorem tailoringCutoff_eq_zero_of_strict_deficit (I : ToricInput n)
    (β : ℝ) (a : Lattice n) (u : RealSpace n)
    (hgap : tailoringWeight β a u < tailoringMaxWeight I β u - Real.sqrt β - 2) :
    tailoringCutoff I β a u = 0 := by
  classical
  obtain ⟨b, hb, hmax⟩ := tailoringMaxWeight_attained I β u
  have hba : b ≠ a := by
    intro he
    subst b
    have := Real.sqrt_nonneg β
    linarith
  unfold tailoringCutoff
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hba, hb⟩)
  apply (tailoringCutoffProfile_eq_zero_iff _).mpr
  rw [hmax]
  linarith

/-- Strict plateau gaps persist on a real open neighborhood and force all
actual augmented cutoffs to keep exactly their current values. -/
theorem tailoringCutoffs_exists_open_constant_of_strict_gaps
    (I : ToricInput n) (β : ℝ) (u : RealSpace n)
    (hgap : ∀ a ∈ tailoringExponents I,
      tailoringWeight β a u < tailoringMaxWeight I β u - Real.sqrt β - 2 ∨
      tailoringMaxWeight I β u - Real.sqrt β < tailoringWeight β a u) :
    ∃ U : Set (RealSpace n), IsOpen U ∧ u ∈ U ∧
      ∀ w ∈ U, ∀ a ∈ tailoringExponents I,
        tailoringCutoff I β a w = tailoringCutoff I β a u := by
  classical
  have hL : Continuous (tailoringMaxWeight I β) :=
    continuous_const.max (I.supportHeight_continuous.sub continuous_const)
  have hw (a : Lattice n) : Continuous (tailoringWeight β a) := by
    unfold tailoringWeight pairing
    fun_prop
  let U : Set (RealSpace n) := {w | ∀ a : {a // a ∈ tailoringExponents I},
    if tailoringWeight β a.val u < tailoringMaxWeight I β u - Real.sqrt β - 2 then
      tailoringWeight β a.val w < tailoringMaxWeight I β w - Real.sqrt β - 2
    else tailoringMaxWeight I β w - Real.sqrt β < tailoringWeight β a.val w}
  have hU : IsOpen U := by
    dsimp [U]
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro a
    split_ifs
    · exact isOpen_lt (hw _) ((hL.sub continuous_const).sub continuous_const)
    · exact isOpen_lt (hL.sub continuous_const) (hw _)
  refine ⟨U, hU, ?_, ?_⟩
  · intro a
    split_ifs with ha
    · exact ha
    · exact (hgap a.val a.property).resolve_left ha
  · intro w hwU a ha
    have hw' := hwU ⟨a, ha⟩
    by_cases hl : tailoringWeight β a u < tailoringMaxWeight I β u - Real.sqrt β - 2
    · simp only [hl, ↓reduceIte] at hw'
      rw [tailoringCutoff_eq_zero_of_strict_deficit I β a w hw',
        tailoringCutoff_eq_zero_of_strict_deficit I β a u hl]
    · simp only [hl, ↓reduceIte] at hw'
      have hu' := (hgap a ha).resolve_left hl
      rw [tailoringCutoff_eq_one_of_gap I β a w (fun b hb =>
        ((sub_le_sub_right (tailoringWeight_le_max I β b hb w) _).trans hw'.le)),
        tailoringCutoff_eq_one_of_gap I β a u (fun b hb =>
        ((sub_le_sub_right (tailoringWeight_le_max I β b hb u) _).trans hu'.le))]

/-- Every actual intrinsic critical point and Liouville zero has strict
plateau gaps for every augmented exponent, uniformly for large parameters. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_strict_gaps
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEndStrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      ((∀ v : N.Tangent z, N.scalarDerivative (fun q => φ (j.map q).1) z v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0) →
      ∀ v ∈ tailoringExponents I,
        tailoringWeight β v (j.map z).1 <
          tailoringMaxWeight I β (j.map z).1 - Real.sqrt β - 2 ∨
        tailoringMaxWeight I β (j.map z).1 - Real.sqrt β <
          tailoringWeight β v (j.map z).1 := by
  obtain ⟨C, hC, B, hB, hcrit⟩ :=
    tailoringEndpoint_exists_uniform_fullFiber_end_critical_conormal_bound
      I hφ hc hU hlower hupper hEnd
  obtain ⟨δ, hδ, B', hB', hsep⟩ :=
    tailoringEndpoint_exists_uniform_closed_strip_conormal_separation I hEndStrong ha hEndLower
  obtain ⟨_, _, B'', _, hrad⟩ :=
    tailoringEndpoint_exists_small_relative_deficit I (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨_, _, hangle⟩ := hEndStrong.exists_coordinateGradient_radial_angle ha hEndLower
  have hlim : Tendsto (fun β : ℝ => C * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, he⟩ := eventually_atTop.mp (hlim.eventually_lt_const hδ)
  refine ⟨max B (max B' (max B'' Be)), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z hcritical v hv
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβB' : B' ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβB'' : B'' ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβBe : Be ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hfiber : tailoringFamily I β 1 (j.map z) = 1 := by
    have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
    rwa [himage] at hmem
  obtain ⟨t, ht⟩ := hcrit β hβB N j himage z hcritical
  have hu := (hrad β hβB'' (j.map z) hfiber).1
  have hp := (hangle (j.map z).1 hu).1
  have hpn : 0 < ‖coordinateGradient φEnd (j.map z).1‖ := norm_pos_iff.mpr hp
  by_contra! hgap
  have hb := hsep β hβB' (j.map z) hfiber ⟨v, hv, hgap⟩ t
  have hstrict := mul_lt_mul_of_pos_right (he β hβBe) hpn
  exact (not_le_of_gt hstrict) (hb.trans ht)

/-- The constant term is uncut at every actual intrinsic critical point,
by the proved small-conormal localization. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_constant_eq_one
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEndStrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      ((∀ v : N.Tangent z, N.scalarDerivative (fun q => φ (j.map q).1) z v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0) →
      tailoringCutoff I β 0 (j.map z).1 = 1 := by
  obtain ⟨C, hC, B, hB, hcrit⟩ :=
    tailoringEndpoint_exists_uniform_fullFiber_end_critical_conormal_bound
      I hφ hc hU hlower hupper hEnd
  obtain ⟨δ, hδ, _, _, _, _, _, _, _, _, B', _, hloc⟩ :=
    tailoringEndpoint_exists_small_conormal_localization I hEndStrong ha hEndLower
  have hlim : Tendsto (fun β : ℝ => C * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, he⟩ := eventually_atTop.mp (hlim.eventually_lt_const hδ)
  refine ⟨max B (max B' Be), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z hz
  have hfiber : tailoringFamily I β 1 (j.map z) = 1 := by
    have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
    rwa [himage] at hmem
  obtain ⟨t, ht⟩ := hcrit β ((le_max_left _ _).trans hβ) N j himage z hz
  apply (hloc β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) (j.map z) hfiber _).2.2.1
  exact ⟨t, ht.trans (mul_le_mul_of_nonneg_right
    (he β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))).le (norm_nonneg _))⟩

/-- An endpoint point with strict cutoff gaps and uncut constant has an
open ambient neighborhood where the actual endpoint function is precisely
the sum of the monomials in its actual retained support. -/
theorem tailoringEndpoint_exists_open_face_equation_of_strict_gaps
    (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (hy : tailoringFamily I β 1 y = 1)
    (hzero : tailoringCutoff I β 0 y.1 = 1)
    (hgap : ∀ a ∈ tailoringExponents I,
      tailoringWeight β a y.1 < tailoringMaxWeight I β y.1 - Real.sqrt β - 2 ∨
      tailoringMaxWeight I β y.1 - Real.sqrt β < tailoringWeight β a y.1) :
    ∃ O : Set (LGSpace n), IsOpen O ∧ y ∈ O ∧
      ∀ w ∈ O,
        tailoringCutoff I β 0 w.1 = 1 ∧
        (∀ v ∈ I.vertices, tailoringCutoff I β v w.1 =
          if v ∈ tailoringRetainedVertices I β y.1 then 1 else 0) ∧
        tailoringFamily I β 1 w =
          ∑ v ∈ tailoringRetainedVertices I β y.1, monomial (Real.exp (-β) : ℂ) v w := by
  classical
  obtain ⟨U, hU, hyU, hconst⟩ :=
    tailoringCutoffs_exists_open_constant_of_strict_gaps I β y.1 hgap
  have hvalues (v : Lattice n) (hv : v ∈ I.vertices) :
      tailoringCutoff I β v y.1 = if v ∈ tailoringRetainedVertices I β y.1 then 1 else 0 := by
    by_cases hr : v ∈ tailoringRetainedVertices I β y.1
    · rw [ite_eq_left hr]
      have hp := ((mem_tailoringRetainedVertices_iff I β y.1 v).mp hr).2
      have hhi : tailoringMaxWeight I β y.1 - Real.sqrt β < tailoringWeight β v y.1 := by
        apply (hgap v (Finset.mem_insert_of_mem hv)).resolve_left
        intro hl
        rw [tailoringCutoff_eq_zero_of_strict_deficit I β v y.1 hl] at hp
        exact lt_irrefl _ hp
      exact tailoringCutoff_eq_one_of_gap I β v y.1 fun b hb =>
        (sub_le_sub_right (tailoringWeight_le_max I β b hb y.1) _).trans hhi.le
    · rw [ite_eq_right hr]
      apply le_antisymm _ (tailoringCutoff_nonneg I β v y.1)
      by_contra! hp
      exact hr ((mem_tailoringRetainedVertices_iff I β y.1 v).mpr ⟨hv, hp⟩)
  have hN : 0 < (I.vertices.card : ℝ) := by exact_mod_cast I.vertices_nonempty.card_pos
  have hS : 2 * tailoringSmallConstant I < tailoringMonomialSize I β y := by
    have hsum := sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β y hy
    rw [hzero, Complex.ofReal_one] at hsum
    have hb := norm_tailoring_weighted_sum_le I β y (tailoringCutoff I β · y.1)
      (fun v _ => ⟨tailoringCutoff_nonneg I β v y.1, tailoringCutoff_le_one I β v y.1⟩)
    change ‖∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y‖ ≤ _ at hb
    rw [hsum, norm_one] at hb
    have hc := tailoringSmallConstant_size I
    have hp := mul_pos hN (tailoringSmallConstant_pos I)
    nlinarith
  let O : Set (LGSpace n) := Prod.fst ⁻¹' U ∩
    {w | 2 * tailoringSmallConstant I < tailoringMonomialSize I β w}
  have hO : IsOpen O := (hU.preimage continuous_fst).inter
    (isOpen_lt continuous_const (contMDiff_tailoringMonomialSize I β).continuous)
  refine ⟨O, hO, ⟨hyU, hS⟩, ?_⟩
  intro w hw
  have hz : tailoringCutoff I β 0 w.1 = 1 :=
    (hconst w.1 hw.1 0 (Finset.mem_insert_self _ _)).trans hzero
  have hv (v : Lattice n) (hv : v ∈ I.vertices) :
      tailoringCutoff I β v w.1 = if v ∈ tailoringRetainedVertices I β y.1 then 1 else 0 :=
    (hconst w.1 hw.1 v (Finset.mem_insert_of_mem hv)).trans (hvalues v hv)
  refine ⟨hz, hv, ?_⟩
  have hη := (tailoringEta_eq_one_iff I β w).mpr hw.2.le
  rw [tailoringFamily_weighted_sum, hη, hz]
  simp only [mul_one, one_mul, Complex.ofReal_one, sub_self, mul_zero, zero_add,
    add_sub_cancel]
  calc
    ∑ v ∈ I.vertices, (tailoringCutoff I β v w.1 : ℂ) * monomial (Real.exp (-β) : ℂ) v w =
        ∑ v ∈ I.vertices, if v ∈ tailoringRetainedVertices I β y.1 then
          monomial (Real.exp (-β) : ℂ) v w else 0 := by
      apply Finset.sum_congr rfl
      intro v hvV
      rw [hv v hvV]
      split_ifs <;> simp
    _ = ∑ v ∈ tailoringRetainedVertices I β y.1, monomial (Real.exp (-β) : ℂ) v w := by
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨tailoringRetainedVertices_subset I β y.1 h, h⟩⟩

/-- The actual full-fiber critical and zero sets lie in constructed open
holomorphic regions with exactly their actual nonempty proper face support. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_holomorphic
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEndStrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      ((∀ v : N.Tangent z, N.scalarDerivative (fun q => φ (j.map q).1) z v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0) →
      ∃ s : Finset (Lattice n),
        s = tailoringRetainedVertices I β (j.map z).1 ∧
        IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices ∧
        ∃ O : Set (LGSpace n), IsOpen O ∧ j.map z ∈ O ∧
          ∀ w ∈ O,
            tailoringCutoff I β 0 w.1 = 1 ∧
            (∀ v ∈ I.vertices, tailoringCutoff I β v w.1 = if v ∈ s then 1 else 0) ∧
            tailoringFamily I β 1 w = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v w := by
  classical
  obtain ⟨B, hB, hgap⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_strict_gaps
    I hφ hc hU hlower hupper hEndStrong ha hEndLower hEnd
  obtain ⟨B', _, hzero⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_constant_eq_one
    I hφ hc hU hlower hupper hEndStrong ha hEndLower hEnd
  obtain ⟨B'', _, hface⟩ := I.exists_tailoringRetainedVertices_face
  refine ⟨max B (max B' B''), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z hz
  have hfiber : tailoringFamily I β 1 (j.map z) = 1 := by
    have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
    rwa [himage] at hmem
  have hzero' := hzero β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ))
    N j himage z hz
  have hgap' := hgap β ((le_max_left _ _).trans hβ) N j himage z hz
  let s := tailoringRetainedVertices I β (j.map z).1
  obtain ⟨t, ht, _, htproper, hst⟩ := hface β
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)) (j.map z).1
  have hsface : IsPolytopeFace I.vertices s := I.isPolytopeFace_subset ht htproper hst
  have hsproper : s ≠ I.vertices := by
    intro he
    exact htproper (Finset.Subset.antisymm ht.1 (he ▸ hst))
  have hsne : s.Nonempty := by
    by_contra! he
    have hsum : ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v (j.map z) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      exact tailoringRetainedMonomial_eq_zero_of_not_mem_support I β (j.map z)
        (Finset.Subset.refl _) hv (by change v ∉ s; rw [he]; simp)
    have hsum' := sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β (j.map z) hfiber
    rw [hsum, hzero', Complex.ofReal_one] at hsum'
    exact zero_ne_one hsum'
  exact ⟨s, rfl, hsface, hsne, hsproper,
    tailoringEndpoint_exists_open_face_equation_of_strict_gaps I β (j.map z) hfiber hzero' hgap'⟩

end FsFltz
