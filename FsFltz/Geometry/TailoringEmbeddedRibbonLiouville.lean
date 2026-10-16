import FsFltz.Geometry.TailoringRibbonLiouvilleFamily

/-!
# Actual Liouville families on supplied tailoring ribbon embeddings

Source: `geometric-part-fsf-proof.tex`, `eq:fiberends`, lines 1208–1237,
and `lem:markedfamily`, lines 975–1009. The supplied embeddings and their
literal full carrier/frontier images are retained. Native tangent kernels,
symplecticity and outwardness are proved from finite toric estimates.
Only one common open extension restriction is made.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- Actual tangent kernels and smooth symplectic primitive data for any
supplied compact ribbon embedding family satisfying the literal level
equation on its carrier. No different embedding family is chosen. -/
theorem tailoringFamily_exists_uniform_embeddedRibbon_primitiveFamily
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n)),
      D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) →
      (∀ t x, x ∈ D.carrier → tailoringFamily I β t.val ((J t).map x) = 1) →
      ∃ O : TopologicalSpace.Opens D.extension.Point, D.carrier ⊆ O ∧
        (∀ t x, x ∈ D.carrier →
          (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
            (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)).ker) ∧
        D.extension.IsSmoothIntervalFormFamily
          (fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) ∧
        ∀ t : Parameter, D.extension.IsSymplecticOn
          (D.extension.exteriorDerivative
            (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ))) O := by
  obtain ⟨_d, _hd, _R, _hR, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨Bπ, hBπ, ?_⟩
  intro β hβ D J hJ hlevel
  have hreg : ∀ t : Parameter, ∀ y, tailoringFamily I β t.val y = 1 →
      Function.Surjective (complexDifferential (lgManifold n) (tailoringFamily I β t.val) y) := by
    intro t y hy
    have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y
    apply (lgManifold n).complexDifferential_surjective_of_planePairing_ne_zero
      (lambdaPotentialForm φ) (tailoringFamily I β t.val) y hnd
    exact ((hπ β hβ t.val t.property y hnd).2.2 (by
      simp only [hy, norm_one, le_refl])).ne'
  have hkernel : ∀ t : Parameter, ∀ x ∈ D.carrier,
      (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
        (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)).ker := by
    intro t
    have h := compactCarrier_embedding_tangent_range (d := 2 * n) (F := ℂ)
    rw [Complex.finrank_real_complex] at h
    exact h D (lgManifold n) (J t) (tailoringFamily I β t.val) 1
      (contMDiff_tailoringFamily_lgManifold I β t.val) (hreg t) (hlevel t)
  let μ : Parameter → D.extension.Form 1 :=
    fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)
  have hα : (lgManifold n).IsSmoothIntervalFormFamily (fun _ : Parameter => lambdaPotentialForm φ) := by
    refine ⟨fun _ => lambdaPotentialForm φ, ?_, fun _ => rfl⟩
    intro a
    refine ⟨univ ×ˢ (chartAt (Model (2 * n)) a).target,
      isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target,
      prod_mono (subset_univ _) Subset.rfl, ?_⟩
    exact ((isSmoothForm_lambdaPotentialForm hφ) a).comp contDiffOn_snd (fun _ hp => hp.2)
  have hμ : D.extension.IsSmoothIntervalFormFamily μ :=
    D.extension.isSmoothIntervalFormFamily_pullback_one (lgManifold n)
      (fun t => (J t).map) hJ (fun _ => lambdaPotentialForm φ) hα
  have hnd : ∀ t : Parameter, ∀ x ∈ D.carrier,
      D.extension.Nondegenerate (D.extension.exteriorDerivative (μ t)) x := by
    intro t x hx
    have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower ((J t).map x)
    apply (lgManifold n).nondegenerate_pullback_of_rankTwo_kernel D.extension (J t)
      (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) x hnd
      (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)))
      (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)))
      ((hπ β hβ t.val t.property ((J t).map x) hnd).2.2 (by
        simp only [hlevel t x hx, norm_one, le_refl])).ne'
    rw [← (lgManifold n).complexDifferential_ker_eq_real_inf_imag]
    exact hkernel t x hx
  obtain ⟨O, hDO, hndO⟩ := D.exists_common_symplecticNeighborhood_of_primitiveFamily μ hμ hnd
  refine ⟨O, hDO, hkernel, hμ, ?_⟩
  intro t
  apply (D.extension.isSymplecticOn_exteriorDerivative_iff (μ t)
    (D.extension.isSmoothForm_of_isSmoothIntervalFormFamily μ hμ t) O).mpr
  exact hndO t

/-- Literal full carrier and frontier images force outwardness for the
actual pulled primitive family on this very supplied compact domain. -/
theorem tailoringFamily_exists_uniform_embeddedRibbon_outwardPrimitiveFamily
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      ∀ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n)),
      D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) →
      (∀ t : Parameter,
        (J t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A} ∧
        (J t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = A}) →
      ∃ O : TopologicalSpace.Opens D.extension.Point, D.carrier ⊆ O ∧
        (∀ t x, x ∈ D.carrier →
          (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
            (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)).ker) ∧
        D.extension.IsSmoothIntervalFormFamily
          (fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) ∧
        (∀ t : Parameter, D.extension.IsSymplecticOn
          (D.extension.exteriorDerivative
            (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ))) O) ∧
        ∀ (t : Parameter) (x : D.extension.Point) (hx : x ∈ frontier D.carrier),
          0 < D.extension.scalarDerivative (D.defining x hx).rho x
            (D.extension.liouvilleVector
              (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) x) := by
  obtain ⟨Bb, hBb, hbase⟩ :=
    tailoringFamily_exists_uniform_embeddedRibbon_primitiveFamily I hφ hc hU hlower hupper
  obtain ⟨F, hF, Be, _hBe, hexhaustion⟩ :=
    tailoringFamily_exists_uniform_whole_end_intrinsic_exhaustion
      I hφ hc hU hlower hupper hEnd hhom hL hend
  obtain ⟨V, hV⟩ := (isCompact_phi0_sublevel (n := n) (L ^ 2 / 2) (by positivity)).bddAbove_image
    (hφ.continuous.comp continuous_fst).continuousOn
  let Bφ : ℝ := (2 * max V 0 + 1) / F
  let β₀ : ℝ := max 1 (max Bb (max Be Bφ))
  refine ⟨F, hF, β₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro β hβ A hA D J hJ himages
  have hβ₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβpos : 0 < β := zero_lt_one.trans_le hβ₁
  have hβbase : Bb ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβend : Be ≤ β := (le_max_left _ _).trans
    ((le_max_right Bb _).trans ((le_max_right 1 _).trans hβ))
  have hβφ : Bφ ≤ β := (le_max_right _ _).trans
    ((le_max_right Bb _).trans ((le_max_right 1 _).trans hβ))
  have hlevel : V < F ^ 2 * β ^ 2 / 2 := by
    have hb : 2 * max V 0 + 1 ≤ F * β := by
      have h := (div_le_iff₀ hF).mp hβφ
      simpa only [mul_comm] using h
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * max V 0 + 1) hb 2
    nlinarith only [hsq, le_max_left V 0, le_max_right V 0, sq_nonneg (max V 0)]
  have hApos : 0 < A := (by positivity : 0 < F ^ 2 * β ^ 2 / 2).trans_le hA
  have hflevel : ∀ t x, x ∈ D.carrier → tailoringFamily I β t.val ((J t).map x) = 1 := by
    intro t x hx
    have hm : (J t).map x ∈ (J t).map '' D.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).1] at hm
    exact hm.1
  obtain ⟨O, hDO, hkernel, hμ, hsymplectic⟩ := hbase β hβbase D J hJ hflevel
  refine ⟨O, hDO, hkernel, hμ, hsymplectic, ?_⟩
  intro t x hx
  have hxD : x ∈ D.carrier := D.compact.isClosed.frontier_subset hx
  have himage : tailoringFamily I β t.val ((J t).map x) = 1 ∧ φ ((J t).map x).1 = A := by
    have hm : (J t).map x ∈ (J t).map '' frontier D.carrier := ⟨x, hx, rfl⟩
    rwa [(himages t).2] at hm
  have hxEnd : L < ‖(WithLp.toLp 2 ((J t).map x).1 : EuclideanSpace ℝ (Fin n))‖ := by
    by_contra hn
    have hsq : realSquaredNorm ((J t).map x).1 ≤ L ^ 2 := by
      simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using
        (sq_le_sq₀ (norm_nonneg _) hL.le).mpr (le_of_not_gt hn)
    have hm : (J t).map x ∈ {y : LGSpace n | phi0 y ≤ L ^ 2 / 2} := by
      change realSquaredNorm ((J t).map x).1 / 2 ≤ L ^ 2 / 2
      linarith only [hsq]
    have hb := hV (mem_image_of_mem (fun y : LGSpace n => φ y.1) hm)
    change φ ((J t).map x).1 ≤ V at hb
    rw [himage.2] at hb
    exact (not_le_of_gt hlevel) (hA.trans hb)
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 ((J t).map x).1)
  have he : metricRadialSq H ((J t).map x).1 = 2 * A := by
    rw [metricRadialSq_potential_eq_two_mul hEnd1 hEnd hhom hc hlower hL hend _ hxEnd, himage.2]
  have hr : F * β ≤ Real.sqrt (metricRadialSq H ((J t).map x).1) := by
    rw [he]
    apply (Real.le_sqrt (mul_nonneg hF.le hβpos.le) (by positivity)).mpr
    nlinarith only [hA]
  have hd := hexhaustion β hβend t.val t.property D.extension (J t) x
    (hkernel t x hxD) hr (by simp only [himage.1, norm_one]; norm_num)
  change metricRadialSq H ((J t).map x).1 / 2 ≤
    D.extension.scalarDerivative (fun y => φ ((J t).map y).1) x
      (D.extension.liouvilleVector
        (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) x) at hd
  rw [he] at hd
  have hout : 0 < D.extension.scalarDerivative (fun y => φ ((J t).map y).1) x
      (D.extension.liouvilleVector
        (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) x) := by
    linarith only [hd, hApos]
  have hvalue := contMDiff_potential_W_level_value hφ (J t)
  have hside : ∀ y ∈ D.carrier, φ ((J t).map y).1 - A ≤ 0 := by
    intro y hy
    have hm : (J t).map y ∈ (J t).map '' D.carrier := ⟨y, hy, rfl⟩
    rw [(himages t).1] at hm
    exact sub_nonpos.mpr hm.2
  have hzero : ∀ y ∈ frontier D.carrier, φ ((J t).map y).1 - A = 0 := by
    intro y hy
    have hm : (J t).map y ∈ (J t).map '' frontier D.carrier := ⟨y, hy, rfl⟩
    rw [(himages t).2] at hm
    exact sub_eq_zero.mpr hm.2
  apply D.outward_of_sublevel_derivative (fun y => φ ((J t).map y).1 - A)
    (hvalue.sub_const A) hside hzero x hx
  unfold scalarDerivative
  change 0 < (show ℝ from mfderiv _ _ ((fun y => φ ((J t).map y).1) - fun _ => A) x _)
  rw [mfderiv_sub (hvalue.mdifferentiableAt (by simp)) mdifferentiableAt_const,
    mfderiv_const, sub_zero]
  exact hout

/-- The supplied ribbon embedding after one common native open restriction.
Its map is literally the old embedding composed with the open inclusion. -/
def tailoringRibbonRestrictedEmbedding
    (D : CompactDomain (2 * n - 2))
    (J : D.extension.SmoothEmbedding (lgManifold n))
    (O : TopologicalSpace.Opens D.extension.Point) (hDO : D.carrier ⊆ O) :
    (D.restrict O hDO).extension.SmoothEmbedding (lgManifold n) where
  map := ⟨fun x => J.map x.val, J.map.contMDiff.comp (D.extension.restrictInclusion O).map.contMDiff⟩
  embedding := J.embedding.comp Topology.IsEmbedding.subtypeVal
  immersion := by
    intro x
    change Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
      (fun y : O => J.map y.val) x)
    rw [D.extension.mfderiv_comp_restrict_val (lgManifold n) O x
      (J.map.contMDiff.mdifferentiableAt (by simp))]
    exact J.immersion x.val

@[simp] theorem tailoringRibbonRestrictedEmbedding_map
    (D : CompactDomain (2 * n - 2))
    (J : D.extension.SmoothEmbedding (lgManifold n))
    (O : TopologicalSpace.Opens D.extension.Point) (hDO : D.carrier ⊆ O)
    (x : (D.restrict O hDO).extension.Point) :
    (tailoringRibbonRestrictedEmbedding D J O hDO).map x = J.map x.val := rfl

/-- One common restriction of the supplied carrier produces actual smooth
Liouville structures and compatible localized completions. The original
embeddings are only precomposed by that native restriction; rank-two
ambient updates pull back to the very same ribbon primitive on the carrier. -/
theorem tailoringFamily_exists_uniform_embeddedRibbon_liouvilleFamily
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      ∀ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n)),
      D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) →
      (∀ t : Parameter,
        (J t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A} ∧
        (J t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = A}) →
      ∃ (O : TopologicalSpace.Opens D.extension.Point) (hDO : D.carrier ⊆ O)
        (Λ : Parameter → LiouvilleStructure (D.restrict O hDO)),
      let E := D.restrict O hDO
      let J' := fun t => tailoringRibbonRestrictedEmbedding D (J t) O hDO
      E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J' t).map) ∧
      (∀ t : Parameter,
        (J' t).map '' E.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A} ∧
        (J' t).map '' frontier E.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = A}) ∧
      (∀ t x, x ∈ E.carrier →
        (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J' t).map x).range =
          (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J' t).map x)).ker) ∧
      (∀ t, (Λ t).primitive =
        E.extension.pullback (lgManifold n) (J' t).map (lambdaPotentialForm φ)) ∧
      (∀ t, (Λ t).field = E.extension.liouvilleVector (Λ t).primitive) ∧
      E.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) ∧
      E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) ∧
      (∀ t : Parameter, E.extension.IsSymplecticOn
        (E.extension.exteriorDerivative (Λ t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily E Λ) ∧
      ∀ (t : Parameter) (K : ℝ) (x : E.extension.Point), x ∈ E.carrier →
        E.extension.pullback (lgManifold n) (J' t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
            (tailoringFamily I β t.val) K) x = (Λ t).primitive x := by
  obtain ⟨F, hF, β₀, hβ₀, hfamily⟩ :=
    tailoringFamily_exists_uniform_embeddedRibbon_outwardPrimitiveFamily
      I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ A hA D J hJ himages
  obtain ⟨O, hDO, hkernel, hμ, hsymplectic, hout⟩ := hfamily β hβ A hA D J hJ himages
  let E := D.restrict O hDO
  let μ : Parameter → D.extension.Form 1 :=
    fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)
  let μ' : Parameter → E.extension.Form 1 :=
    fun t => E.extension.pullback D.extension Subtype.val (μ t)
  have hsm (t : Parameter) : D.extension.IsSmoothForm (μ t) :=
    D.extension.isSmoothForm_of_isSmoothIntervalFormFamily μ hμ t
  have hsm' (t : Parameter) : E.extension.IsSmoothForm (μ' t) :=
    E.extension.isSmoothForm_pullback_one D.extension
      (D.extension.restrictInclusion O).map (μ t) (hsm t)
  have hnd' (t : Parameter) (x : E.extension.Point) :
      E.extension.Nondegenerate (E.extension.exteriorDerivative (μ' t)) x := by
    intro v hv
    apply (hsymplectic t).2.2 x.val x.property v
    intro w
    have heq := hv w
    unfold evalTwo at heq ⊢
    rw [D.extension.exteriorDerivative_restrict O (μ t) (hsm t) x] at heq
    exact heq
  have hglobal (t : Parameter) : E.extension.IsSymplecticOn
      (E.extension.exteriorDerivative (μ' t)) univ :=
    (E.extension.isSymplecticOn_exteriorDerivative_iff _ (hsm' t) _).mpr
      (fun x _ => hnd' t x)
  have hfield (t : Parameter) (x : E.extension.Point) :
      E.extension.liouvilleVector (μ' t) x = D.extension.liouvilleVector (μ t) x.val := by
    apply E.extension.liouvilleVector_eq (μ' t) x (hnd' t x)
    intro v
    dsimp only [μ']
    unfold evalTwo evalOne
    erw [D.extension.exteriorDerivative_restrict O (μ t) (hsm t) x,
      D.extension.pullback_restrict_val O (μ t) x]
    exact D.extension.liouvilleVector_contraction (μ t) x.val
      (D.extension.liouvilleEquation_exists (μ t) x.val
        ((hsymplectic t).2.2 x.val x.property)) v
  let Λ : Parameter → LiouvilleStructure E := fun t =>
    { primitive := μ' t
      smooth_primitive := hsm' t
      symplectic := ⟨(hglobal t).1, fun x _ => (hglobal t).2.1 x (mem_univ _),
        fun x _ => (hglobal t).2.2 x (mem_univ _)⟩
      field := E.extension.liouvilleVector (μ' t)
      smooth_field := E.extension.isSmoothVectorField_liouvilleVector _ (hsm' t) (hnd' t)
      contraction := fun x _ => E.extension.liouvilleVector_contraction _ x
        (E.extension.liouvilleEquation_exists _ x (hnd' t x))
      outward := by
        intro x hx
        have hx' : x.val ∈ frontier D.carrier := by
          rw [D.frontier_restrict_carrier O] at hx
          exact hx
        let B := D.defining x.val hx'
        have hρ := (B.smooth_rho.contMDiffAt
          (B.open_neighbourhood.mem_nhds B.mem_neighbourhood)).mdifferentiableAt (by simp)
        change (0 : ℝ) < (show ℝ from mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ)
          (fun y : O => B.rho y.val) x (E.extension.liouvilleVector (μ' t) x))
        rw [hfield t x]
        have hchain := mfderiv_comp (f := (Subtype.val : O → D.extension.Point))
          (g := B.rho) x hρ
          ((D.extension.restrictInclusion O).map.contMDiff.mdifferentiableAt (by simp))
        erw [D.extension.mfderiv_restrict_val O x] at hchain
        exact (congrArg (fun T => (T (D.extension.liouvilleVector (μ t) x.val) : ℝ))
          hchain).trans_gt (hout t x.val hx') }
  let J' := fun t => tailoringRibbonRestrictedEmbedding D (J t) O hDO
  have hJ' : E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J' t).map) :=
    E.extension.isSmoothIntervalMapFamily_comp_of_contMDiff_family D.extension (lgManifold n)
      (fun t => (J t).map) hJ (fun _ x => x.val)
      (contMDiff_subtype_val.comp contMDiff_snd)
  have hJkernel : ∀ t x, x ∈ E.carrier →
      (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J' t).map x).range =
        (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J' t).map x)).ker := by
    intro t x hx
    change (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
      (fun y : O => (J t).map y.val) x).range = _
    rw [D.extension.mfderiv_comp_restrict_val (lgManifold n) O x
      ((J t).map.contMDiff.mdifferentiableAt (by simp))]
    exact hkernel t x.val hx
  have hprimitive (t : Parameter) : (Λ t).primitive =
      E.extension.pullback (lgManifold n) (J' t).map (lambdaPotentialForm φ) := by
    change E.extension.pullback D.extension Subtype.val
      (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) = _
    exact (E.extension.pullback_comp D.extension (lgManifold n)
      (u := (Subtype.val : O → D.extension.Point)) (v := (J t).map)
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)).mdifferentiable (by simp))
      ((J t).map.contMDiff.mdifferentiable (by simp)) (lambdaPotentialForm φ)).symm
  have hΛ : E.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) :=
    E.extension.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family D.extension
      (fun _ x => x.val) (contMDiff_subtype_val.comp contMDiff_snd) μ hμ
  have hΛfield : E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) :=
    E.extension.isSmoothIntervalVectorFieldFamily_liouvilleVector μ' hΛ hnd'
  refine ⟨O, hDO, Λ, hJ', ?_, hJkernel, hprimitive, fun _ => rfl, hΛ, hΛfield, hglobal,
    E.exists_smooth_localizedCompletionFamily_of_liouvilleFamily Λ hΛ, ?_⟩
  · intro t
    constructor
    · change ((J t).map ∘ (Subtype.val : O → D.extension.Point)) ''
        (Subtype.val ⁻¹' D.carrier) = _
      rw [image_comp, D.image_restrict_carrier O hDO]
      exact (himages t).1
    · rw [D.frontier_restrict_carrier O]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hm : (J t).map x.val ∈ (J t).map '' frontier D.carrier := ⟨x.val, hx, rfl⟩
        rwa [(himages t).2] at hm
      · intro hy
        have hm : y ∈ (J t).map '' frontier D.carrier := by rwa [(himages t).2]
        obtain ⟨x, hx, heq⟩ := hm
        exact ⟨⟨x, hDO (D.compact.isClosed.frontier_subset hx)⟩, hx, heq⟩
  · intro t k x hx
    rw [hprimitive]
    exact E.extension.pullback_rankTwoPrimitive_eq_of_tangent_range_le_kernel (lgManifold n)
      (J' t) (lambdaPotentialForm φ) (tailoringFamily I β t.val) k x (le_of_eq (hJkernel t x hx))

end FsFltz
