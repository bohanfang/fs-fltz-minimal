import FsFltz.Geometry.TailoringMarkedPrefixNativeHits
import FsFltz.Geometry.SmoothFlowBoundaryDerivative
import FsFltz.Geometry.TailoringAmbientRayPositivity

/-!
# One native open neighborhood of outer hitting times

Source: `geometric-part-fsf-proof.tex`, `lem:hitting`, lines 1760–1775,
and `prop:band`, lines 1778–1817. Smooth local times descend through the
actual logarithmic cover and agree by uniqueness on an open coefficient
neighborhood. Their union is an actual open subset of coefficient times
the quotient ambient, with one smooth time and one literal spatial map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Manifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance outerHittingNeighborhoodCharts :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance outerHittingNeighborhoodSmooth :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- A smooth logarithmic local hitting time descends through an actual
smooth local inverse of the quotient cover. -/
theorem exists_native_local_hitting_time_of_logarithmic
    {G : Flow ℝ (ℝ × LGSpace n)}
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    {φ : RealSpace n → ℝ} {A K : ℝ} {x : TangentCoordinates n}
    {V : Set (ℝ × TangentCoordinates n)} (hV : IsOpen V) (hxV : (K, x) ∈ V)
    {τ : ℝ × TangentCoordinates n → ℝ} (hτ : ContDiffOn ℝ ∞ τ V)
    (hhit : ∀ p ∈ V, φ (G (τ p) (p.1, lgCover p.2)).2.1 = A) :
    ∃ W : Set (ℝ × LGSpace n), IsOpen W ∧ (K, lgCover x) ∈ W ∧
      ∃ σ : ℝ × LGSpace n → ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ σ W ∧
        σ (K, lgCover x) = τ (K, x) ∧
        (∀ p ∈ W, φ (G (σ p) p).2.1 = A) ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          𝓘(ℝ, Model (2 * n)) ∞ (fun p => (G (σ p) p).2) W := by
  let l := isLocalDiffeomorph_lgCover n x
  let S : Set (ℝ × LGSpace n) := univ ×ˢ l.localInverse.source
  let ψ : ℝ × LGSpace n → ℝ × TangentCoordinates n :=
    fun p => (p.1, l.localInverse p.2)
  have hS : IsOpen S := isOpen_univ.prod l.localInverse.open_source
  have hψ₂ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, TangentCoordinates n) ∞ (fun p : ℝ × LGSpace n => l.localInverse p.2) S :=
    l.localInverse.contMDiffOn.comp contMDiff_snd.contMDiffOn
      (fun (p : ℝ × LGSpace n) (hp : p ∈ S) => hp.2)
  have hψ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ × TangentCoordinates n) ∞ ψ S :=
    contMDiff_fst.contMDiffOn.prodMk_space hψ₂
  let W : Set (ℝ × LGSpace n) := S ∩ ψ ⁻¹' V
  let σ : ℝ × LGSpace n → ℝ := τ ∘ ψ
  have hW : IsOpen W := hψ.continuousOn.isOpen_inter_preimage hS hV
  have hcenter : ψ (K, lgCover x) = (K, x) :=
    Prod.ext rfl (l.localInverse_left_inv l.localInverse_mem_target)
  have hτM : ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, ℝ) ∞ τ V :=
    contMDiffOn_iff_contDiffOn.mpr hτ
  have hσ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ σ W :=
    hτM.comp (hψ.mono inter_subset_left) (fun p hp => hp.2)
  have hxW : (K, lgCover x) ∈ W := by
    refine ⟨⟨mem_univ _, l.localInverse_mem_source⟩, ?_⟩
    change ψ (K, lgCover x) ∈ V
    rw [hcenter]
    exact hxV
  refine ⟨W, hW, hxW,
    σ, hσ, congrArg τ hcenter, ?_, ?_⟩
  · intro p hp
    have he := hhit (ψ p) hp.2
    simpa only [ψ, σ, Function.comp_apply, l.localInverse_right_inv hp.1.2] using he
  · intro p hp
    exact (hG.comp_contMDiffOn (hσ.prodMk contMDiff_id.contMDiffOn) p hp).snd

/-- Local smooth roots glue on their native open union whenever roots
are unique for every initial point on an open coefficient neighborhood. -/
theorem exists_native_open_smooth_hitting_time_of_unique
    {G : Flow ℝ (ℝ × LGSpace n)}
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    {φ : RealSpace n → ℝ} {A : ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hunique : ∀ K ∈ J, ∀ y : LGSpace n, ∀ s t : ℝ,
      φ (G s (K, y)).2.1 = A → φ (G t (K, y)).2.1 = A → s = t)
    {S : Set (ℝ × LGSpace n)} (hSJ : ∀ p ∈ S, p.1 ∈ J)
    (hlocal : ∀ p ∈ S, ∃ U : Set (ℝ × LGSpace n), IsOpen U ∧ p ∈ U ∧
      ∃ σ : ℝ × LGSpace n → ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ σ U ∧
        ∀ q ∈ U, φ (G (σ q) q).2.1 = A) :
    ∃ W : Set (ℝ × LGSpace n), IsOpen W ∧ S ⊆ W ∧ W ⊆ J ×ˢ univ ∧
      ∃ τ : ℝ × LGSpace n → ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W ∧
        (∀ p ∈ W, φ (G (τ p) p).2.1 = A) ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          𝓘(ℝ, Model (2 * n)) ∞ (fun p => (G (τ p) p).2) W := by
  classical
  choose U hU hmem σ hσ hlevel using fun p : S => hlocal p.val p.property
  let W : Set (ℝ × LGSpace n) := ⋃ p : S, U p ∩ (J ×ˢ univ)
  let τ : ℝ × LGSpace n → ℝ := fun p =>
    if h : ∃ t : ℝ, φ (G t p).2.1 = A then h.choose else 0
  have hW : IsOpen W := isOpen_iUnion fun p => (hU p).inter (hJ.prod isOpen_univ)
  have hhit : ∀ p ∈ W, φ (G (τ p) p).2.1 = A := by
    intro p hp
    obtain ⟨a, ha, _⟩ := mem_iUnion.mp hp
    have he : ∃ t : ℝ, φ (G t p).2.1 = A := ⟨σ a p, hlevel a p ha⟩
    simp only [τ, dite_eq_left he]
    exact he.choose_spec
  have hτ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W := by
    intro p hp
    obtain ⟨a, ha, hJa⟩ := mem_iUnion.mp hp
    have hpa : p ∈ U a ∩ (J ×ˢ univ) := ⟨ha, hJa⟩
    have heq : τ =ᶠ[𝓝 p] σ a := by
      filter_upwards [((hU a).inter (hJ.prod isOpen_univ)).mem_nhds hpa] with q hq
      have hqW : q ∈ W := mem_iUnion.mpr ⟨a, hq⟩
      exact hunique q.1 hq.2.1 q.2 (τ q) (σ a q) (hhit q hqW) (hlevel a q hq.1)
    exact ((hσ a).contMDiffAt ((hU a).mem_nhds ha)).congr_of_eventuallyEq heq
      |>.contMDiffWithinAt
  refine ⟨W, hW, ?_, ?_, τ, hτ, hhit, ?_⟩
  · intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hmem ⟨p, hp⟩, hSJ p hp, mem_univ _⟩
  · intro p hp
    obtain ⟨a, _, hJa⟩ := mem_iUnion.mp hp
    exact hJa
  · intro p hp
    exact (hG.comp_contMDiffOn (hτ.prodMk contMDiff_id.contMDiffOn) p hp).snd

/-- Finite toric input constructs one positive smooth time on an actual
open coefficient/quotient neighborhood of the entire core interval.
Its restrictions are the proved bijections to the same retained marked
outer boundary, with the same full embedded ribbon core. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_open_transverse_hits
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
                    ∀ k ∈ Icc (0 : ℝ) K,
                      (∀ y ∈ tailoringCoreSection I φEnd β,
                        (∀ s, φ (G s (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 → s = τ (k, y)) ∧
                        ∀ s ∈ Icc (0 : ℝ) (τ (k, y)), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
                          1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        (tailoringLegendreConic I φEnd ∩
                          range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                            P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map) := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, c, U, hc, hU, hlower, hupper,
    ⟨L, hL, hend⟩, Aamb, Cminus, Cplus, Bprefix, hamb, hCminus, hCminusCplus,
    hBprefix, hprefix⟩ := I.exists_uniform_original_marked_prefix_fullCore_native_hits
  obtain ⟨Bdomain, _hBdomain, hdomain⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hstrong.smooth hstrong.homogeneous hL hend
      (hCminus.trans hCminusCplus)
  obtain ⟨Btrans, _hBtrans, htrans⟩ :=
    tailoringEndpoint_exists_uniform_coreSection_outward_allK_transverse
      I hφ hc hU hlower hupper hstrong hL hend
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, max Bprefix (max Bdomain Btrans),
    hamb, hCminus, hCminusCplus, hBprefix.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β ((le_max_left _ _).trans hβ)
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst, hnative, htimes⟩ :=
    hprefix originalK hK
  let A : ℝ := Cplus ^ 2 * β ^ 2 / 2
  have hβD : Bdomain ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβT : Btrans ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
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
  refine ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst, hnative, hcoreTrans,
    Wplus, hWplus, hproductWplus, τ, hτ.mono inter_subset_left,
    (fun p hp => ⟨hp.2, hhit p hp.1⟩), hmap.mono inter_subset_left, ?_⟩
  intro k hk
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

/-- Finite toric input constructs one positive smooth time on an actual
open coefficient/quotient neighborhood of the entire core interval.
Its restrictions are the proved bijections to the same retained marked
outer boundary, with the same full embedded ribbon core. -/
theorem ToricInput.exists_uniform_original_marked_prefix_fullCore_native_open_hits
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
              ∃ G : Flow ℝ (ℝ × LGSpace n),
                ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
                  ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
                  (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2) ∧
                (∀ t p, (G t p).1 = p.1) ∧
                (∀ k ∈ Icc (0 : ℝ) K, ∀ y t, φ (G t (k, y)).2.1 ≤ Cplus ^ 2 * β ^ 2 / 2 →
                  IsMIntegralCurveAt (fun s => (G s (k, y)).2)
                    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                      (lambdaPotentialForm φ) (tailoringFamily I β 1) k)) t) ∧
                ∃ W : Set (ℝ × LGSpace n), IsOpen W ∧
                  Icc (0 : ℝ) K ×ˢ tailoringCoreSection I φEnd β ⊆ W ∧
                  ∃ τ : ℝ × LGSpace n → ℝ,
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W ∧
                    (∀ p ∈ W, 0 < τ p ∧ φ (G (τ p) p).2.1 = Cplus ^ 2 * β ^ 2 / 2) ∧
                    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
                      𝓘(ℝ, Model (2 * n)) ∞ (fun p => (G (τ p) p).2) W ∧
                    ∀ k ∈ Icc (0 : ℝ) K,
                      (∀ y ∈ tailoringCoreSection I φEnd β,
                        (∀ s, φ (G s (k, y)).2.1 = Cplus ^ 2 * β ^ 2 / 2 → s = τ (k, y)) ∧
                        ∀ s ∈ Icc (0 : ℝ) (τ (k, y)), (G s (k, y)).2 ∈ tailoringLegendreConic I φEnd ∧
                          1 ≤ (tailoringFamily I β 1 (G s (k, y)).2).re) ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = Cplus ^ 2 * β ^ 2 / 2} ∧
                      BijOn (fun y => (G (τ (k, y)) (k, y)).2) (tailoringCoreSection I φEnd β)
                        (tailoringLegendreConic I φEnd ∩
                          range (P.marked.tailoring_ambient_marking.nativeEmbedding.comp
                            P.marked.tailoring_ambient_marking.domain.boundaryInclusion).map) := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, hprefix⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore_native_open_transverse_hits
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, B,
    hamb, hCminus, hCminusCplus, hB, ?_⟩
  intro β hβ
  obtain ⟨hR, hset, hfib, hprefix⟩ := hprefix β hβ
  refine ⟨hR, hset, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst,
    hnative, _hcoreTrans, W, hW, hproductW, τ, hτ, hhit, hmap, htimes⟩ := hprefix originalK hK
  exact ⟨K, hKpos, hKL, m, hm, P, hcoreP, hboundaryP, G, hG, hfst,
    hnative, W, hW, hproductW, τ, hτ, hhit, hmap, htimes⟩

end FsFltz
