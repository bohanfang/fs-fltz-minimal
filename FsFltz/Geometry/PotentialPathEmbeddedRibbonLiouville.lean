import FsFltz.Geometry.PotentialPathRoundedMotionFiber
import FsFltz.Geometry.PotentialFiberRegular
import FsFltz.Geometry.TailoringEmbeddedRibbonLiouville
import FsFltz.Geometry.CompactPrimitiveFamilyRestriction
import FsFltz.Geometry.PotentialPathPrimitiveFamily

/-!
# Native Liouville data on the same holomorphic path ribbon

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169;
`geometric-part-fsf-proof.tex`, `lem:markedfamily` and its application,
lines 975–1049, and assembly, lines 2127–2158. The actual coefficient and
potential vary together. Supplied compact carrier and embedding witnesses
are retained, using only one common restriction of the native extension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

/-- The literal level equation on the same supplied native carrier determines
its tangent kernel. The actual varying potential primitive is jointly smooth
and symplectic on one common open neighborhood of that carrier. -/
theorem ToricInput.coefficientPath_potentialPath_exists_uniform_embeddedRibbon_primitiveFamily
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n)),
      D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) →
      (∀ t x, x ∈ D.carrier →
        W (I.alongCoefficientPath t.val) ((J t).map x) = (Real.exp β : ℂ)) →
      ∃ O : TopologicalSpace.Opens D.extension.Point, D.carrier ⊆ O ∧
        (∀ t x, x ∈ D.carrier →
          (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
            (complexDifferential (lgManifold n)
              (W (I.alongCoefficientPath t.val)) ((J t).map x)).ker) ∧
        D.extension.IsSmoothIntervalFormFamily
          (fun t => D.extension.pullback (lgManifold n) (J t).map
            (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))) ∧
        ∀ t : Parameter, D.extension.IsSymplecticOn
          (D.extension.exteriorDerivative
            (D.extension.pullback (lgManifold n) (J t).map
              (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)))) O := by
  obtain ⟨B, hB, hapos⟩ := I.coefficientPath_a_pos_of_large_value
  let β₀ : ℝ := max 1 (Real.log (B + 1))
  refine ⟨β₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ D J hJ hlevel
  have hexp : B < Real.exp β := by
    have h := Real.exp_le_exp.mpr ((le_max_right _ _).trans hβ)
    rw [Real.exp_log (by linarith : 0 < B + 1)] at h
    linarith
  have hnorm : ‖(Real.exp β : ℂ)‖ = Real.exp β := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos β)]
  have ha : ∀ t : Parameter, ∀ y,
      W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) →
      0 < a (I.alongCoefficientPath t.val) y := by
    intro t y hy
    exact hapos t.val t.property y (by rwa [hy, hnorm])
  have hreg : ∀ t : Parameter, ∀ y,
      W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) →
      Function.Surjective (complexDifferential (lgManifold n)
        (W (I.alongCoefficientPath t.val)) y) := by
    intro t y hy
    exact complexDifferential_W_surjective_of_a_pos _ y (ha t y hy)
  have hkernel : ∀ t : Parameter, ∀ x ∈ D.carrier,
      (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
        (complexDifferential (lgManifold n)
          (W (I.alongCoefficientPath t.val)) ((J t).map x)).ker := by
    intro t
    have h := compactCarrier_embedding_tangent_range (d := 2 * n) (F := ℂ)
    rw [Complex.finrank_real_complex] at h
    exact h D (lgManifold n) (J t) (W (I.alongCoefficientPath t.val)) (Real.exp β : ℂ)
      (contMDiff_W_lgManifold _) (hreg t) (hlevel t)
  let ψ : Parameter → RealSpace n → ℝ :=
    fun t => potentialPath (fun u => realSquaredNorm u / 2) φ t.val
  let μ : Parameter → D.extension.Form 1 :=
    fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm (ψ t))
  have hα : (lgManifold n).IsSmoothIntervalFormFamily
      (fun t => lambdaPotentialForm (ψ t)) :=
    ⟨fun t => lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t),
      isSmoothFormFamily_lambdaPotentialForm_potentialPath
        (contDiff_realSquaredNorm.div_const 2) hφ, fun _ => rfl⟩
  have hμ : D.extension.IsSmoothIntervalFormFamily μ :=
    D.extension.isSmoothIntervalFormFamily_pullback_one (lgManifold n)
      (fun t => (J t).map) hJ (fun t => lambdaPotentialForm (ψ t)) hα
  have hnd : ∀ t : Parameter, ∀ x ∈ D.carrier,
      D.extension.Nondegenerate (D.extension.exteriorDerivative (μ t)) x := by
    intro t x hx
    have hψ := potentialPath_native_contDiff hφ t.val
    have hcl : 0 < min 1 c := lt_min zero_lt_one hc
    have hcu : 0 < max 1 U := zero_lt_one.trans_le (le_max_left _ _)
    have hl := potentialPath_native_hessian_lowerBound hφ hlower t.property
    have hu := potentialPath_native_hessian_upperBound hφ hupper t.property
    have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hψ hcl hl ((J t).map x)
    apply (lgManifold n).nondegenerate_pullback_of_rankTwo_kernel D.extension (J t)
      (lambdaPotentialForm (ψ t)) (isSmoothForm_lambdaPotentialForm hψ) x hnd
      (Complex.reCLM.comp (complexDifferential (lgManifold n)
        (W (I.alongCoefficientPath t.val)) ((J t).map x)))
      (Complex.imCLM.comp (complexDifferential (lgManifold n)
        (W (I.alongCoefficientPath t.val)) ((J t).map x)))
      (planePairing_potential_W_pos hψ hcl hcu hl hu (I.alongCoefficientPath t.val)
        ((J t).map x) (ha t _ (hlevel t x hx)) hnd).ne'
    rw [← (lgManifold n).complexDifferential_ker_eq_real_inf_imag]
    exact hkernel t x hx
  obtain ⟨O, hDO, hndO⟩ := D.exists_common_symplecticNeighborhood_of_primitiveFamily μ hμ hnd
  refine ⟨O, hDO, hkernel, hμ, ?_⟩
  intro t
  apply (D.extension.isSymplecticOn_exteriorDerivative_iff (μ t)
    (D.extension.isSmoothForm_of_isSmoothIntervalFormFamily μ hμ t) O).mpr
  exact hndO t

/-- Both literal image equations derive outwardness for the canonical field
of the varying pulled primitive, on this very supplied native carrier. -/
theorem ToricInput.coefficientPath_potentialPath_exists_uniform_embeddedRibbon_outwardPrimitiveFamily
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
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
      ∀ β ≥ β₀, ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus →
      ∀ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n)),
      D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) →
      (∀ t : Parameter,
        (J t).map '' D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
          potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
        (J t).map '' frontier D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
          potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus}) →
      ∃ O : TopologicalSpace.Opens D.extension.Point, D.carrier ⊆ O ∧
        (∀ t x, x ∈ D.carrier →
          (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
            (complexDifferential (lgManifold n)
              (W (I.alongCoefficientPath t.val)) ((J t).map x)).ker) ∧
        D.extension.IsSmoothIntervalFormFamily
          (fun t => D.extension.pullback (lgManifold n) (J t).map
            (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))) ∧
        (∀ t : Parameter, D.extension.IsSymplecticOn
          (D.extension.exteriorDerivative
            (D.extension.pullback (lgManifold n) (J t).map
              (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)))) O) ∧
        ∀ (t : Parameter) (x : D.extension.Point) (hx : x ∈ frontier D.carrier),
          0 < D.extension.scalarDerivative (D.defining x hx).rho x
            (D.extension.liouvilleVector
              (D.extension.pullback (lgManifold n) (J t).map
                (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))) x) := by
  obtain ⟨Bb, hBb, hbase⟩ :=
    ToricInput.coefficientPath_potentialPath_exists_uniform_embeddedRibbon_primitiveFamily I hφ hc hlower hupper
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφE := hφ.comp e.contDiff
  have hEndE := hEnd1.comp e.contDiff
  have hEndsE : ∀ u ≠ 0, ContDiffAt ℝ ∞ (φEnd ∘ e) u := by
    intro u hu
    apply (hEnd (e u) (by
      intro hz
      apply hu
      apply e.injective
      simpa only [map_zero] using hz)).comp u e.contDiff.contDiffAt
  have hhomE : ∀ r : ℝ, 0 < r → ∀ u, (φEnd ∘ e) (r • u) = r ^ 2 * (φEnd ∘ e) u := by
    intro r hr u
    simpa only [Function.comp_apply, map_smul] using hhom r hr (e u)
  have hendE : ∀ u, L ≤ ‖u‖ → (φ ∘ e) u = (φEnd ∘ e) u := by
    intro u hu
    exact hend (e u) hu
  obtain ⟨F, hF, Be, hBe, hexhaustion⟩ :=
    I.coefficientPath_potentialPath_intrinsic_fiber_outward
      hφE hEndE hEndsE hhomE hc hlower hupper hL hendE 0
  refine ⟨F, hF, max Bb Be, hBb.trans_le (le_max_left _ _), ?_⟩
  intro β hβ Aminus hA D J hJ himages
  have hlevel : ∀ t x, x ∈ D.carrier →
      W (I.alongCoefficientPath t.val) ((J t).map x) = (Real.exp β : ℂ) := by
    intro t x hx
    have hm : (J t).map x ∈ (J t).map '' D.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).1] at hm
    exact hm.1
  obtain ⟨O, hDO, hkernel, hμ, hsymplectic⟩ :=
    hbase β ((le_max_left _ _).trans hβ) D J hJ hlevel
  refine ⟨O, hDO, hkernel, hμ, hsymplectic, ?_⟩
  intro t x hx
  have hxD : x ∈ D.carrier := D.compact.isClosed.frontier_subset hx
  let ψ := potentialPath (fun u => realSquaredNorm u / 2) φ t.val
  have himage : W (I.alongCoefficientPath t.val) ((J t).map x) = (Real.exp β : ℂ) ∧
      ψ ((J t).map x).1 = Aminus := by
    have hm : (J t).map x ∈ (J t).map '' frontier D.carrier := ⟨x, hx, rfl⟩
    rwa [(himages t).2] at hm
  have hψeq : potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) t.val ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm = ψ := by
    funext u
    change (1 - t.val) * (‖e.symm u‖ ^ 2 / 2) + t.val * φ (e (e.symm u)) =
      (1 - t.val) * (realSquaredNorm u / 2) + t.val * φ u
    rw [e.apply_symm_apply]
    congr 2
    simp [e, EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hout := ((hexhaustion β ((le_max_right _ _).trans hβ)).2 t.val t.property
    t.val t.property (2 * n - 2) D.extension (J t) x (hkernel t x hxD)
    (by simpa only [hψeq, himage.2] using hA)
    (by rw [himage.1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos β)])).2
  have hout' : 0 < D.extension.scalarDerivative (fun y => ψ ((J t).map y).1) x
      (D.extension.liouvilleVector
        (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm ψ)) x) := by
    change 0 < D.extension.scalarDerivative
      ((fun y => (potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) t.val ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) y.1) ∘ (J t).map) x
      (D.extension.liouvilleVector
        (D.extension.pullback (lgManifold n) (J t).map
          (lambdaPotentialForm (potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) t.val ∘
            (EuclideanSpace.equiv (Fin n) ℝ).symm))) x) at hout
    rw [hψeq] at hout
    exact hout
  have hvalue := contMDiff_potential_W_level_value (potentialPath_native_contDiff hφ t.val) (J t)
  have hside : ∀ y ∈ D.carrier, ψ ((J t).map y).1 - Aminus ≤ 0 := by
    intro y hy
    have hm : (J t).map y ∈ (J t).map '' D.carrier := ⟨y, hy, rfl⟩
    rw [(himages t).1] at hm
    exact sub_nonpos.mpr hm.2
  have hzero : ∀ y ∈ frontier D.carrier, ψ ((J t).map y).1 - Aminus = 0 := by
    intro y hy
    have hm : (J t).map y ∈ (J t).map '' frontier D.carrier := ⟨y, hy, rfl⟩
    rw [(himages t).2] at hm
    exact sub_eq_zero.mpr hm.2
  apply D.outward_of_sublevel_derivative (fun y => ψ ((J t).map y).1 - Aminus)
    (hvalue.sub_const Aminus) hside hzero x hx
  unfold scalarDerivative
  change 0 < (show ℝ from mfderiv _ _ ((fun y => ψ ((J t).map y).1) - fun _ => Aminus) x _)
  rw [mfderiv_sub (hvalue.mdifferentiableAt (by simp)) mdifferentiableAt_const,
    mfderiv_const, sub_zero]
  exact hout'

/-- Construct native outward Liouville and localized completion families on
one common restriction of the same supplied holomorphic path ribbon.
Every embedding witness and both full image equations are preserved, and
all ambient base coefficients pull back to the actual varying primitive. -/
theorem ToricInput.coefficientPath_potentialPath_exists_uniform_embeddedRibbon_liouvilleFamily
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
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
      ∀ β ≥ β₀, ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus →
      ∀ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n)),
      D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) →
      (∀ t : Parameter,
        (J t).map '' D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
          potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
        (J t).map '' frontier D.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
          potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus}) →
      ∃ (O : TopologicalSpace.Opens D.extension.Point) (hDO : D.carrier ⊆ O)
        (Λ : Parameter → LiouvilleStructure (D.restrict O hDO)),
      let E := D.restrict O hDO
      let J' := fun t => tailoringRibbonRestrictedEmbedding D (J t) O hDO
      E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J' t).map) ∧
      (∀ t : Parameter,
        (J' t).map '' E.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
          potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ Aminus} ∧
        (J' t).map '' frontier E.carrier = {y | W (I.alongCoefficientPath t.val) y = (Real.exp β : ℂ) ∧
          potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 = Aminus}) ∧
      (∀ t x, x ∈ E.carrier →
        (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J' t).map x).range =
          (complexDifferential (lgManifold n)
            (W (I.alongCoefficientPath t.val)) ((J' t).map x)).ker) ∧
      (∀ t, (Λ t).primitive = E.extension.pullback (lgManifold n) (J' t).map
        (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))) ∧
      (∀ t, (Λ t).field = E.extension.liouvilleVector (Λ t).primitive) ∧
      E.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) ∧
      E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) ∧
      (∀ t : Parameter, E.extension.IsSymplecticOn
        (E.extension.exteriorDerivative (Λ t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily E Λ) ∧
      ∀ (t : Parameter) (K : ℝ) (x : E.extension.Point), x ∈ E.carrier →
        E.extension.pullback (lgManifold n) (J' t).map
          ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
            (W (I.alongCoefficientPath t.val)) K) x = (Λ t).primitive x := by
  obtain ⟨F, hF, β₀, hβ₀, hfamily⟩ :=
    ToricInput.coefficientPath_potentialPath_exists_uniform_embeddedRibbon_outwardPrimitiveFamily
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ Aminus hA D J hJ himages
  obtain ⟨O, hDO, hkernel, hμ, hsymplectic, hout⟩ := hfamily β hβ Aminus hA D J hJ himages
  let E := D.restrict O hDO
  let μ : Parameter → D.extension.Form 1 :=
    fun t => D.extension.pullback (lgManifold n) (J t).map
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
  obtain ⟨Λ, hprimitiveRestricted, hfield, hΛ, hΛfield, hglobal, hcompletion⟩ :=
    D.exists_restricted_liouvilleFamily_of_outwardPrimitiveFamily μ hμ O hDO hsymplectic hout
  let J' := fun t => tailoringRibbonRestrictedEmbedding D (J t) O hDO
  have hJ' : E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J' t).map) :=
    E.extension.isSmoothIntervalMapFamily_comp_of_contMDiff_family D.extension (lgManifold n)
      (fun t => (J t).map) hJ (fun _ x => x.val)
      (contMDiff_subtype_val.comp contMDiff_snd)
  have hJkernel : ∀ t x, x ∈ E.carrier →
      (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J' t).map x).range =
        (complexDifferential (lgManifold n)
          (W (I.alongCoefficientPath t.val)) ((J' t).map x)).ker := by
    intro t x hx
    change (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
      (fun y : O => (J t).map y.val) x).range = _
    rw [D.extension.mfderiv_comp_restrict_val (lgManifold n) O x
      ((J t).map.contMDiff.mdifferentiableAt (by simp))]
    exact hkernel t x.val hx
  have hprimitive (t : Parameter) : (Λ t).primitive =
      E.extension.pullback (lgManifold n) (J' t).map
        (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val)) := by
    rw [hprimitiveRestricted t]
    exact (E.extension.pullback_comp D.extension (lgManifold n)
      (u := (Subtype.val : O → D.extension.Point)) (v := (J t).map)
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)).mdifferentiable (by simp))
      ((J t).map.contMDiff.mdifferentiable (by simp))
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))).symm
  refine ⟨O, hDO, Λ, hJ', ?_, hJkernel, hprimitive, hfield, hΛ, hΛfield, hglobal, hcompletion, ?_⟩
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
      (J' t) (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
      (W (I.alongCoefficientPath t.val)) k x (le_of_eq (hJkernel t x hx))

end FsFltz.Geometry
