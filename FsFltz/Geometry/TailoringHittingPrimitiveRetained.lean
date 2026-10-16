import FsFltz.Geometry.TailoringHittingPrimitive

/-!
# The retained finite-input outer hitting primitive

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1778–1817,
`eq:hittingprimitive`, lines 1847–1853; `geoemtric-part-fsf.tex`,
`thm:target`, lines 352–435. One selected potential, prefix, cutoff action,
hitting time and full-fiber embedding neighborhood are retained throughout.
Native nondegeneracy and boundary positivity come from their finite analytic
producers for that same potential. The primitive law is a conclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology
namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance retainedHittingPrimitiveCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance retainedHittingPrimitiveSmooth :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- Finite toric input constructs the actual retained outer hitting data
and proves its exponential primitive law on the same full-fiber neighborhood.
Neither a native complete-flow identification nor a primitive law is input. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_primitives_with_legendre
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      Nonempty (RetainedLegendrePotential φEnd φ) ∧
      ∃ Aamb Cminus Cplus β₀ : ℝ, AmbientEndBound I Aamb ∧
        0 < Cminus ∧ Cminus < Cplus ∧ 0 < β₀ ∧ ∀ β ≥ β₀,
        max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
        RatioSetWellDefined I (Real.exp β) ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp β) Afib ∧
          Afib < Cminus ^ 2 * β ^ 2 / 2) ∧
        ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
          ∃ K : ℝ, 0 < K ∧ originalK ≤ K / Real.exp β ^ 2 ∧
          ∃ m : RoundingChoice,
            GeometricAdmissibleRounding I (Real.exp β) originalK
              (Cminus ^ 2 * β ^ 2 / 2) (Cplus ^ 2 * β ^ 2 / 2) m ∧
            ∃ P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m,
              ((P.marked.tailoring.embedding parameterOne).comp
                (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
                  P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
                P.marked.tailoring.deformation.target.ribbonCompletion.core =
                  tailoringCoreSection I φEnd β ∧
              range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map =
                  {z | φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β 1) k)) y) ∧
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                φ y.1 = Cplus ^ 2 * β ^ 2 / 2 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y)) ∧
              ∃ G : Flow ℝ (ℝ × LGSpace n),
                ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
                  ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
                  (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2) ∧
                (∀ t p, (G t p).1 = p.1) ∧
                (∀ k ∈ Icc (0 : ℝ) K, ∀ y t, φ (G t (k, y)).2.1 ≤ Cplus ^ 2 * β ^ 2 / 2 →
                  IsMIntegralCurveAt (fun s => (G s (k, y)).2)
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k)) t) ∧
                (∀ k ∈ Icc (0 : ℝ) K, ∀ y ∈ tailoringCoreSection I φEnd β,
                  0 < deriv (fun t => (tailoringFamily I β 1 (G t (k, y)).2).re) 0) ∧
                ∃ W : Set (ℝ × LGSpace n), IsOpen W ∧
                  Icc (0 : ℝ) K ×ˢ tailoringCoreSection I φEnd β ⊆ W ∧
                  ∃ τ : ℝ × LGSpace n → ℝ,
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W ∧
                    (∀ p ∈ W, 0 < τ p ∧ φ (G (τ p) p).2.1 = Cplus ^ 2 * β ^ 2 / 2) ∧
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
                      𝓘(ℝ, Model (2 * n)) ∞ (fun p => (G (τ p) p).2) W ∧
                    (∀ k ∈ Icc (0 : ℝ) K,
                      (∀ y ∈ tailoringCoreSection I φEnd β,
                        (∀ s, φ (G s (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 → s = τ (k, y)) ∧
                        ∀ s ∈ Icc (0 : ℝ) (τ (k, y)), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
                          1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        (tailoringLegendreConic I φEnd ∩
                          range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                            P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map)) ∧
                    let Q := P.marked.tailoring.ribbon_marking parameterOne
                    ∃ (V : TopologicalSpace.Opens ℝ)
                      (U : TopologicalSpace.Opens Q.manifold.Point),
                      Icc (0 : ℝ) K ⊆ V ∧
                      Q.embedding.map ⁻¹' tailoringCoreSection I φEnd β ⊆ U ∧
                      (∀ p ∈ (V : Set ℝ) ×ˢ (U : Set Q.manifold.Point),
                        (p.1, Q.embedding.map p.2) ∈ W) ∧
                      ∃ J : V → (Q.manifold.restrict U).SmoothEmbedding (lgManifold n),
                        (∀ k x, (J k).map x =
                          (G (τ (k.val, Q.embedding.map x.val))
                            (k.val, Q.embedding.map x.val)).2) ∧
                        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
                          𝓘(ℝ, Model (2 * n)) ∞
                          (fun p : ℝ × Q.manifold.Point =>
                            (G (τ (p.1, Q.embedding.map p.2))
                              (p.1, Q.embedding.map p.2)).2)
                          ((V : Set ℝ) ×ˢ (U : Set Q.manifold.Point)) ∧
                        ∀ k ∈ Icc (0 : ℝ) K, ∀ x ∈ (U : Set Q.manifold.Point),
                          Q.manifold.pullback (lgManifold n)
                            (fun y => (G (τ (k, Q.embedding.map y))
                              (k, Q.embedding.map y)).2)
                            ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                              (tailoringFamily I β 1) k) x =
                                Real.exp (τ (k, Q.embedding.map x)) •
                                  Q.manifold.pullback (lgManifold n) Q.embedding.map
                                    (lambdaPotentialForm φ) x := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, hLegendre, c, U, hc, hU, hlower, hupper,
    ⟨L, hL, hend⟩, Aamb, Cminus, Cplus, Bprefix, hamb, hCminus, hCminusCplus,
    hBprefix, hprefix⟩ := I.exists_uniform_original_marked_prefix_fullCore_native_hits_with_legendre
  obtain ⟨Bdomain, _hBdomain, hdomain⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hstrong.smooth hstrong.homogeneous hL hend
      (hCminus.trans hCminusCplus)
  obtain ⟨Btrans, _hBtrans, htrans⟩ :=
    tailoringEndpoint_exists_uniform_coreSection_outward_allK_transverse
      I hφ hc hU hlower hupper hstrong hL hend
  obtain ⟨Bsymp, _hBsymp, hsymp⟩ :=
    tailoringFamily_exists_uniform_symplectic I hφ hc hU hlower hupper
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, hLegendre, Aamb, Cminus, Cplus,
    max Bprefix (max Bdomain (max Btrans Bsymp)),
    hamb, hCminus, hCminusCplus, hBprefix.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β ((le_max_left _ _).trans hβ)
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst, hnative, htimes⟩ :=
    hprefix originalK hK
  let A : ℝ := Cplus ^ 2 * β ^ 2 / 2
  have hβD : Bdomain ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβT : Btrans ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβS : Bsymp ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβpos : 0 < β := hBprefix.trans_le ((le_max_left _ _).trans hβ)
  have houter : Cminus ^ 2 * β ^ 2 / 2 < Cplus ^ 2 * β ^ 2 / 2 := by gcongr
  have hcoreBelow : ∀ y ∈ tailoringCoreSection I φEnd β, φ y.1 < A := by
    intro y hy
    rw [← hcoreP] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxImage : ((P.marked.tailoring.embedding parameterOne).comp
        (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
          P.marked.tailoring.deformation.target.ribbonEmbedding)).map x ∈
        ((P.marked.tailoring.embedding parameterOne).comp
          (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
            P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
          P.marked.tailoring.deformation.target.ribbonDomain.domain.carrier := ⟨x, hx.1, rfl⟩
    have himage := P.marked.tailoring.ribbon_image parameterOne
    change ((P.marked.tailoring.embedding parameterOne).comp
        (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
          P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
        P.marked.tailoring.deformation.target.ribbonDomain.domain.carrier = _ at himage
    rw [himage] at hxImage
    exact hxImage.2.trans_lt houter
  have hcoreTrans : ∀ k ∈ Icc (0 : ℝ) K, ∀ y ∈ tailoringCoreSection I φEnd β,
      0 < deriv (fun t => (tailoringFamily I β 1 (G t (k, y)).2).re) 0 := by
    intro k hk y hy
    obtain ⟨d, hd, hdf⟩ := htrans β hβT y hy 1 le_rfl k hk.1
    have hdf' : complexDifferential (lgManifold n) (tailoringFamily I β 1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y) = (d : ℂ) := by
      have hy' : ((1 : ℝ) • y.1, y.2) = y := by simp only [one_smul, Prod.eta]
      exact hy' ▸ hdf
    have hcurve := hnative k hk y 0
      (by simpa only [Flow.map_zero_apply] using (hcoreBelow y hy).le)
    have hder := hasDerivAt_re_of_isMIntegralCurveAt (lgManifold n)
      (contMDiff_tailoringFamily_lgManifold I β 1) hcurve
    have hz : (G 0 (k, y)).2 = y := congrArg Prod.snd (G.map_zero_apply (k, y))
    have hdf0 := hz.symm ▸ hdf'
    rw [hder.deriv, hdf0, Complex.ofReal_re]
    exact hd
  obtain ⟨hcompact, _, hboundary⟩ := hdomain β hβD
  have hND : ∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
      (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
          (tailoringFamily I β 1) k)) y := by
    intro k hk y
    exact (hsymp β hβS 1 (by simp) k hk).2.2 y (mem_univ _)
  have hOut : ∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n, φ y.1 = A →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y) := by
    intro k hk y hy
    have hp := (hboundary 1 (by simp) k hk).2 y (sub_eq_zero.mpr hy)
    let D : (lgManifold n).Tangent y →L[ℝ] ℝ :=
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => φ z.1 - A) y
    let Dφ : (lgManifold n).Tangent y →L[ℝ] ℝ :=
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => φ z.1) y
    let Dc : (lgManifold n).Tangent y →L[ℝ] ℝ :=
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun _ : LGSpace n => A) y
    have he : D = Dφ - Dc :=
      mfderiv_sub ((contMDiff_potentialValue hφ).mdifferentiableAt (x := y) (by simp))
        (mdifferentiableAt_const (I := 𝓘(ℝ, Model (2 * n))) (c := A))
    have hz : Dc = 0 := mfderiv_const
    rw [hz, sub_zero] at he
    have hval := congrArg (fun L : (lgManifold n).Tangent y →L[ℝ] ℝ =>
      L ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y)) he
    exact lt_of_lt_of_eq hp hval
  have hS : IsCompact {y : LGSpace n | φ y.1 = A} :=
    hcompact.of_isClosed_subset
      (isClosed_eq (hφ.continuous.comp continuous_fst) continuous_const)
      (fun y hy => sub_nonpos.mpr hy.le)
  have hpos : ∀ k ∈ Icc (0 : ℝ) K, ∀ y : LGSpace n, φ y.1 = A →
      0 < deriv (fun t => φ (G t (k, y)).2.1) 0 := by
    intro k hk y hy
    have hg : Differentiable ℝ (fun t => φ (G t (k, y)).2.1) :=
      ((contMDiff_potentialValue hφ).comp
        (hG.comp (contMDiff_id.prodMk contMDiff_const)).snd).contDiff.differentiable (by simp)
    have hd := hasDerivAt_scalar_of_isMIntegralCurveAt (lgManifold n)
      (ρ := fun z => φ z.1 - A) ((contMDiff_potentialValue hφ).sub contMDiff_const)
      (hnative k hk y 0 (by simpa only [Flow.map_zero_apply] using hy.le))
    have hd' : HasDerivAt (fun t => φ (G t (k, y)).2.1 - A)
        (deriv (fun t => φ (G t (k, y)).2.1) 0) 0 := (hg 0).hasDerivAt.sub_const A
    rw [hd'.unique hd]
    have hz : (G 0 (k, y)).2 = y := congrArg Prod.snd (G.map_zero_apply (k, y))
    exact hz.symm ▸ (hboundary 1 (by simp) k hk.1).2 y (sub_eq_zero.mpr hy)
  obtain ⟨J, hJ, hPJ, hunique⟩ := exists_isOpen_parameter_unique_flow_hits G hG hfst
    (contMDiff_potentialValue hφ) isCompact_Icc hS hpos
  have hlocal : ∀ p ∈ Icc (0 : ℝ) K ×ˢ tailoringCoreSection I φEnd β,
      ∃ U : Set (ℝ × LGSpace n), IsOpen U ∧ p ∈ U ∧
        ∃ σ : ℝ × LGSpace n → ℝ,
          ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ σ U ∧
          ∀ q ∈ U, φ (G (σ q) q).2.1 = A := by
    rintro ⟨k, y⟩ ⟨hk, hy⟩
    obtain ⟨x, rfl⟩ := lgCover_surjective n y
    obtain ⟨τ₀, _hτ₀, _hbij, _hbijP, hsmooth⟩ := htimes k hk
    obtain ⟨V, hV, hxV, σlog, hσlog, _hcenter, hhit, _hmap⟩ := hsmooth x hy
    obtain ⟨U, hU, hpoint, σ, hσ, _hcenter, hhit, _hmap⟩ :=
      exists_native_local_hitting_time_of_logarithmic hG hV hxV hσlog hhit
    exact ⟨U, hU, hpoint, σ, hσ, hhit⟩
  obtain ⟨W, hW, hproductW, _hWJ, τ, hτ, hhit, hmap⟩ :=
    exists_native_open_smooth_hitting_time_of_unique hG hJ hunique
      (fun p hp => hPJ hp.1) hlocal
  have hrestriction (k : ℝ) (hk : k ∈ Icc (0 : ℝ) K) :
      ∃ τ₀ : LGSpace n → ℝ,
        (∀ y ∈ tailoringCoreSection I φEnd β, τ (k, y) = τ₀ y) ∧
        (∀ y ∈ tailoringCoreSection I φEnd β,
          0 < τ₀ y ∧ φ (G (τ₀ y) (k, y)).2.1 = A ∧
          (∀ s, φ (G s (k, y)).2.1 = A → s = τ₀ y) ∧
          ∀ s ∈ Icc (0 : ℝ) (τ₀ y), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
            1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
        BijOn (fun y => (G (τ₀ y) (k, y)).2) (tailoringCoreSection I φEnd β)
          {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = A} ∧
        BijOn (fun y => (G (τ₀ y) (k, y)).2) (tailoringCoreSection I φEnd β)
          (tailoringLegendreConic I φEnd ∩
            range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
              P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map) := by
    obtain ⟨τ₀, hτ₀, hbij, hbijP, _hsmooth⟩ := htimes k hk
    refine ⟨τ₀, ?_, hτ₀, hbij, hbijP⟩
    intro y hy
    exact hunique k (hPJ hk) y (τ (k, y)) (τ₀ y)
      (hhit (k, y) (hproductW ⟨hk, hy⟩)) (hτ₀ y hy).2.1
  let Wplus : Set (ℝ × LGSpace n) := W ∩ τ ⁻¹' Ioi (0 : ℝ)
  have hWplus : IsOpen Wplus :=
    hτ.continuousOn.isOpen_inter_preimage hW isOpen_Ioi
  have hproductWplus : Icc (0 : ℝ) K ×ˢ tailoringCoreSection I φEnd β ⊆ Wplus := by
    intro p hp
    obtain ⟨τ₀, heq, hτ₀, _⟩ := hrestriction p.1 hp.1
    refine ⟨hproductW hp, ?_⟩
    change 0 < τ p
    simpa only [← heq p.2 hp.2, Prod.mk.eta] using (hτ₀ p.2 hp.2).1
  refine ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, hND, hOut, G, hG, hfst, hnative, hcoreTrans,
    Wplus, hWplus, hproductWplus, τ, hτ.mono inter_subset_left,
    (fun p hp => ⟨hp.2, hhit p hp.1⟩), hmap.mono inter_subset_left, ?_, ?_⟩
  · intro k hk
    obtain ⟨τ₀, heq, hτ₀, hbij, hbijP⟩ := hrestriction k hk
    have hmapEq : EqOn (fun y => (G (τ₀ y) (k, y)).2)
        (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β) := by
      intro y hy
      change (G (τ₀ y) (k, y)).2 = (G (τ (k, y)) (k, y)).2
      rw [heq y hy]
    refine ⟨?_, hbij.congr hmapEq, hbijP.congr hmapEq⟩
    intro y hy
    rw [heq y hy]
    exact (hτ₀ y hy).2.2
  · let Q := P.marked.tailoring.ribbon_marking parameterOne
    obtain ⟨V, U, hPV, hcoreU, hVU, Jemb, hJemb, hsmooth⟩ :=
      Q.exists_uniform_outer_hitting_embeddings
        (contMDiff_tailoringFamily_lgManifold I β 1) hcoreP G hG hfst
        isCompact_Icc hWplus hproductWplus (hτ.mono inter_subset_left)
        (fun k hk => by
          obtain ⟨τ₀, heq, _hτ₀, hbij, _hbijP⟩ := hrestriction k hk
          apply hbij.injOn.congr
          intro y hy
          simp only [heq y hy]) hcoreTrans
    refine ⟨V, U, hPV, hcoreU, hVU, Jemb, hJemb, hsmooth, ?_⟩
    intro k hk x hx
    apply Q.native_hitting_pullback_at
      (contMDiff_tailoringFamily_lgManifold I β 1) hφ A k
      (fun y _ => hND k hk.1 y) G hG (hnative k hk) (hOut k hk.1)
      hWplus (hτ.mono inter_subset_left)
      (fun p hp => ⟨hp.2, hhit p hp.1⟩)
    exact hVU (k, x) ⟨hPV hk, hx⟩

/-- The established interface retains the same witnesses by projection. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_hitting_primitives
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      ∃ Aamb Cminus Cplus β₀ : ℝ, AmbientEndBound I Aamb ∧
        0 < Cminus ∧ Cminus < Cplus ∧ 0 < β₀ ∧ ∀ β ≥ β₀,
        max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
        RatioSetWellDefined I (Real.exp β) ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp β) Afib ∧
          Afib < Cminus ^ 2 * β ^ 2 / 2) ∧
        ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
          ∃ K : ℝ, 0 < K ∧ originalK ≤ K / Real.exp β ^ 2 ∧
          ∃ m : RoundingChoice,
            GeometricAdmissibleRounding I (Real.exp β) originalK
              (Cminus ^ 2 * β ^ 2 / 2) (Cplus ^ 2 * β ^ 2 / 2) m ∧
            ∃ P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m,
              ((P.marked.tailoring.embedding parameterOne).comp
                (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
                  P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
                P.marked.tailoring.deformation.target.ribbonCompletion.core =
                  tailoringCoreSection I φEnd β ∧
              range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map =
                  {z | φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
                  ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                    (tailoringFamily I β 1) k)) y) ∧
              (∀ k : ℝ, 0 ≤ k → ∀ y : LGSpace n,
                φ y.1 = Cplus ^ 2 * β ^ 2 / 2 →
                  0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k) y)) ∧
              ∃ G : Flow ℝ (ℝ × LGSpace n),
                ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
                  ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
                  (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2) ∧
                (∀ t p, (G t p).1 = p.1) ∧
                (∀ k ∈ Icc (0 : ℝ) K, ∀ y t, φ (G t (k, y)).2.1 ≤ Cplus ^ 2 * β ^ 2 / 2 →
                  IsMIntegralCurveAt (fun s => (G s (k, y)).2)
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k)) t) ∧
                (∀ k ∈ Icc (0 : ℝ) K, ∀ y ∈ tailoringCoreSection I φEnd β,
                  0 < deriv (fun t => (tailoringFamily I β 1 (G t (k, y)).2).re) 0) ∧
                ∃ W : Set (ℝ × LGSpace n), IsOpen W ∧
                  Icc (0 : ℝ) K ×ˢ tailoringCoreSection I φEnd β ⊆ W ∧
                  ∃ τ : ℝ × LGSpace n → ℝ,
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W ∧
                    (∀ p ∈ W, 0 < τ p ∧ φ (G (τ p) p).2.1 = Cplus ^ 2 * β ^ 2 / 2) ∧
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
                      𝓘(ℝ, Model (2 * n)) ∞ (fun p => (G (τ p) p).2) W ∧
                    (∀ k ∈ Icc (0 : ℝ) K,
                      (∀ y ∈ tailoringCoreSection I φEnd β,
                        (∀ s, φ (G s (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 → s = τ (k, y)) ∧
                        ∀ s ∈ Icc (0 : ℝ) (τ (k, y)), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
                          1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        (tailoringLegendreConic I φEnd ∩
                          range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                            P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map)) ∧
                    let Q := P.marked.tailoring.ribbon_marking parameterOne
                    ∃ (V : TopologicalSpace.Opens ℝ)
                      (U : TopologicalSpace.Opens Q.manifold.Point),
                      Icc (0 : ℝ) K ⊆ V ∧
                      Q.embedding.map ⁻¹' tailoringCoreSection I φEnd β ⊆ U ∧
                      (∀ p ∈ (V : Set ℝ) ×ˢ (U : Set Q.manifold.Point),
                        (p.1, Q.embedding.map p.2) ∈ W) ∧
                      ∃ J : V → (Q.manifold.restrict U).SmoothEmbedding (lgManifold n),
                        (∀ k x, (J k).map x =
                          (G (τ (k.val, Q.embedding.map x.val))
                            (k.val, Q.embedding.map x.val)).2) ∧
                        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
                          𝓘(ℝ, Model (2 * n)) ∞
                          (fun p : ℝ × Q.manifold.Point =>
                            (G (τ (p.1, Q.embedding.map p.2))
                              (p.1, Q.embedding.map p.2)).2)
                          ((V : Set ℝ) ×ˢ (U : Set Q.manifold.Point)) ∧
                        ∀ k ∈ Icc (0 : ℝ) K, ∀ x ∈ (U : Set Q.manifold.Point),
                          Q.manifold.pullback (lgManifold n)
                            (fun y => (G (τ (k, Q.embedding.map y))
                              (k, Q.embedding.map y)).2)
                            ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                              (tailoringFamily I β 1) k) x =
                                Real.exp (τ (k, Q.embedding.map x)) •
                                  Q.manifold.pullback (lgManifold n) Q.embedding.map
                                    (lambdaPotentialForm φ) x := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, _hLegendre, rest⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_hitting_primitives_with_legendre
  exact ⟨φEnd, φ, hstrong, hEnd1, hφ, rest⟩

end FsFltz
