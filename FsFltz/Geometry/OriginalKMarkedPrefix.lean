import FsFltz.Geometry.PotentialTailoringOriginalAssembly

/-!
# Common rounding for the original-K marked prefix

Source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435, and
`sec:lean`, lines 766–836; `geometric-part-fsf-proof.tex`,
`lem:choices`, lines 950–973, `lem:markedfamily`, lines 975–1009,
and `sec:assembly`, lines 2123–2166 and 2195–2208.
The original quadratic endpoint supplies a logarithmic full-fiber bound.
One proved width serves the original coefficient path and both retained
marked families. The five-arrow prefix starts at a constructed convenient
original pair; attachment of an arbitrary supplied initial tuple remains
the separate initial-choice comparison obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- The original threshold and the retained marked-family widths have a
positive common lower choice. Every thinner supplied profile works for
all larger original coefficients and the same actual marked prefix.
The arbitrary initial-choice comparison is not assumed or discharged. -/
theorem coefficientPath_tailoring_exists_uniform_original_marked_prefix
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
    ∃ Aamb F : ℝ, AmbientEndBound I Aamb ∧ 0 < F ∧
      ∀ Cplus : ℝ, F < Cplus → ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
      RatioSetWellDefined I (Real.exp β) ∧
      FiberEndBound I Aamb (Real.exp β) (F ^ 2 * β ^ 2 / 2) ∧
      ∃ Kstar : ℝ, 0 < Kstar ∧
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 < Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
      GeometricAdmissibleRounding I (Real.exp β) originalK Aminus
        (Cplus ^ 2 * β ^ 2 / 2) m ∧
      ∀ K : ℝ, Kstar ≤ K → originalK ≤ K / Real.exp β ^ 2 →
        Nonempty (PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m) := by
  obtain ⟨Aamb, R0, hamb, hR0, hbounds⟩ := I.exists_initial_analytic_bounds
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hEndE : ∀ u ≠ 0, ContDiffAt ℝ ∞ (φEnd ∘ e) u := by
    intro u hu
    exact (hEnd (e u) (by simpa [e] using hu)).comp u e.contDiff.contDiffAt
  have hhomE : ∀ r : ℝ, 0 < r → ∀ u, (φEnd ∘ e) (r • u) = r ^ 2 * (φEnd ∘ e) u := by
    intro r hr u
    simp only [Function.comp_apply, map_smul]
    exact hhom r hr (e u)
  have hendE : ∀ u, L ≤ ‖u‖ → (φ ∘ e) u = (φEnd ∘ e) u := by
    intro u hu
    exact hend (e u) (by change L ≤ ‖u‖; exact hu)
  obtain ⟨FO, hFO, BO, hBO, horiginal⟩ := I.exists_original_logarithmic_fiberEndBound
    (hφ.comp e.contDiff) (hEnd1.comp e.contDiff) hEndE hhomE hc hlower hupper hL hendE Aamb
  obtain ⟨FP, hFP, hprefix⟩ := coefficientPath_tailoring_exists_uniform_marked_prefix
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  let F := max FO FP
  refine ⟨Aamb, F, hamb, hFO.trans_le (le_max_left _ _), ?_⟩
  intro Cplus hCplus
  obtain ⟨BP, hBP, hprefix⟩ := hprefix Cplus ((le_max_right _ _).trans_lt hCplus)
  let β₀ := max BO (max BP (Real.log R0 + 1))
  refine ⟨β₀, hBO.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβO : BO ≤ β := (le_max_left _ _).trans hβ
  have hβP : BP ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hR0pos : 0 < R0 := (zero_lt_one.trans_le (le_max_left _ _)).trans hR0
  have hlog : Real.log R0 < β := by
    have hh := (le_max_right BP (Real.log R0 + 1)).trans
      ((le_max_right BO _).trans hβ)
    linarith
  have hR0β : R0 < Real.exp β := (Real.log_lt_iff_lt_exp hR0pos).mp hlog
  obtain ⟨hne, hbdd, _⟩ := hbounds (Real.exp β) hR0β.le
  have hset : RatioSetWellDefined I (Real.exp β) := ⟨hne, hbdd⟩
  have hfibO := horiginal β hβO
  have hFOlevel : FO ^ 2 * β ^ 2 / 2 ≤ F ^ 2 * β ^ 2 / 2 := by
    dsimp [F]
    gcongr
    exact le_max_left FO FP
  have hfib : FiberEndBound I Aamb (Real.exp β) (F ^ 2 * β ^ 2 / 2) :=
    ⟨hfibO.1.trans hFOlevel, fun y hy hW => hfibO.2 y (hFOlevel.trans hy) hW⟩
  obtain ⟨Kstar, hKstar, _hthreshold, hprefix⟩ := hprefix β hβP
  refine ⟨hR0.trans hR0β, hset, hfib, Kstar, hKstar, ?_⟩
  intro Aminus hlevel houter
  have hFPlevel : FP ^ 2 * β ^ 2 / 2 ≤ Aminus := by
    apply le_trans _ hlevel.le
    dsimp [F]
    gcongr
    exact le_max_right FO FP
  obtain ⟨δP, hδP, _hgapP, hprefix⟩ := hprefix Aminus hFPlevel houter
  obtain ⟨δO, hδO, hgapO, hround⟩ := exists_original_admissible_rounding_width
    I hamb (hR0.trans hR0β) hset le_rfl hfib hlevel houter
  refine ⟨min δO δP, lt_min hδO hδP, (min_le_left _ _).trans_lt hgapO, ?_⟩
  intro m hm hmd originalK hK
  have hround0 := hround m hm (hmd.trans (min_le_left _ _))
  have hK0 : 0 ≤ K0 I (Real.exp β) :=
    zero_le_one.trans (one_le_K0 I (Real.exp β) hset.1 hset.2)
  have hroundK := GeometricAdmissibleRounding.mono_parameter I hK0 hK hround0
  refine ⟨hroundK, ?_⟩
  intro K hKstar' hKL
  obtain ⟨P⟩ := hprefix m hm (hmd.trans (min_le_right _ _)) K hKstar'
  obtain ⟨T, _⟩ := P.exists_original_augmentation hamb (hR0.trans hR0β)
    hset hK hKL hfib hlevel hroundK
  exact ⟨T⟩

/- The next consumer selects the potential, the convenient levels, the
common profile, and a finite normalized coefficient from the toric input. -/

/-- Every supplied original coefficient in range admits an actual convenient
five-arrow marked prefix, with the same first arrow carrying the logarithmic
grading. The source is constructed at the convenient levels; this theorem
does not compare an independently supplied arbitrary initial tuple to it. -/
theorem ToricInput.exists_uniform_original_k_marked_prefix (I : ToricInput n) :
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
            Nonempty (PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m) := by
  obtain ⟨φEnd, φ, hstrong, hEnd1, hφ, ⟨L, hL, hend, _hendpath⟩, _hpathhom,
    _hpathsmooth, c, U, hc, hU, hess⟩ := I.exists_compatiblePotential_with_uniform_path
  have hessOne := hess 1 (by simp)
  have hψone : potentialPath (fun u => realSquaredNorm u / 2) φ 1 = φ := by
    funext u
    simp [potentialPath]
  rw [hψone] at hessOne
  obtain ⟨Aamb, F, hamb, hF, hprefix⟩ :=
    coefficientPath_tailoring_exists_uniform_original_marked_prefix
      I hφ hc hU (fun u v => (hessOne u v).1) (fun u v => (hessOne u v).2)
      hEnd1 hstrong.smooth hstrong.homogeneous hL hend
  let Cminus := F + 1
  let Cplus := F + 2
  have hCminus : 0 < Cminus := by dsimp [Cminus]; linarith
  have hFCminus : F < Cminus := by dsimp [Cminus]; linarith
  have hCminusCplus : Cminus < Cplus := by dsimp [Cminus, Cplus]; linarith
  obtain ⟨β₀, hβ₀, hprefix⟩ := hprefix Cplus (hFCminus.trans hCminusCplus)
  refine ⟨φEnd, φ, hstrong, hEnd1, hφ, Aamb, Cminus, Cplus, β₀,
    hamb, hCminus, hCminusCplus, hβ₀, ?_⟩
  intro β hβ
  have hβpos := hβ₀.trans_le hβ
  obtain ⟨hR, hset, hfib, Kstar, hKstar, hprefix⟩ := hprefix β hβ
  have hlevel : F ^ 2 * β ^ 2 / 2 < Cminus ^ 2 * β ^ 2 / 2 := by
    gcongr
  have houter : Cminus ^ 2 * β ^ 2 / 2 < Cplus ^ 2 * β ^ 2 / 2 := by
    gcongr
  obtain ⟨δ, hδ, _hgap, hprefix⟩ := hprefix (Cminus ^ 2 * β ^ 2 / 2) hlevel houter
  refine ⟨hR, hset, ⟨F ^ 2 * β ^ 2 / 2, hfib, hlevel⟩, ?_⟩
  intro originalK hK
  let K := max Kstar (originalK * Real.exp β ^ 2)
  have hKpos : 0 < K := hKstar.trans_le (le_max_left _ _)
  have hKL : originalK ≤ K / Real.exp β ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos β))).mpr (le_max_right _ _)
  let m : RoundingChoice := ⟨δ, roundingProfile δ hδ⟩
  obtain ⟨hm, hprefix⟩ := hprefix m hδ le_rfl originalK hK
  exact ⟨K, hKpos, hKL, m, hm, hprefix K (le_max_left _ _) hKL⟩

end FsFltz
