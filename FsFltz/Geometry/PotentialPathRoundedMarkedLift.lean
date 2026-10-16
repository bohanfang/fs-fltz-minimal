import FsFltz.Geometry.PotentialPathHorizontalGluing

/-!
# One simultaneous lift of the literal rounded holomorphic pair

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
matching truncations, lines 1010–1049, and assembly, lines 2127–2158.
Finite analytic data construct every local solution and its compatible
open germs. Affine gluing retains the rounded boundary, full truncated
fiber, and its actual moving-potential frontier in one smooth field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance roundedLiftLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance roundedLiftLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth
local instance roundedLiftProdCharts : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
local instance roundedLiftProdSmooth : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))

/-- One constructed native field on the actual compact rounded pair family,
with open differential collars for all three marked boundaries. Ambient
regularity is produced by the finite-input Liouville estimate; no local
lift, compatibility certificate, or trivialization is an input. -/
theorem ToricInput.coefficientPath_potentialPath_exists_uniform_rounded_marked_horizontalField
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
    ∃ F : ℝ, 0 < F ∧ ∀ D : ℝ, F < D →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (O Bambient Bribbon Bfrontier : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          potentialPath_roundedDefiningFunction I φ (Real.exp β) (D ^ 2 * β ^ 2 / 2) m p ≤ 0} ⊆ O ∧
        IsOpen Bambient ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          potentialPath_roundedDefiningFunction I φ (Real.exp β) (D ^ 2 * β ^ 2 / 2) m p = 0} ⊆ Bambient ∧
        IsOpen Bribbon ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          W (I.alongCoefficientPath p.1) p.2 = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 ≤ Aminus} ⊆ Bribbon ∧
        IsOpen Bfrontier ∧
        {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          W (I.alongCoefficientPath p.1) p.2 = (Real.exp β : ℂ) ∧ potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 = Aminus} ⊆ Bfrontier ∧
        ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
          (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) ∧
        (∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (Prod.fst : ℝ × LGSpace n → ℝ) p (V p) = (1 : ℝ)) ∧
        (∀ p ∈ O ∩ Bambient, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × LGSpace n => potentialPath_roundedDefiningFunction I φ (Real.exp β)
            (D ^ 2 * β ^ 2 / 2) m q) p (V p) = 0) ∧
        (∀ p ∈ O ∩ Bribbon, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
          (fun q : ℝ × LGSpace n => (q.1, W (I.alongCoefficientPath q.1) q.2)) p (V p) = (1, 0)) ∧
        ∀ p ∈ O ∩ Bfrontier, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × LGSpace n => potentialPath (fun u => realSquaredNorm u / 2) φ q.1 q.2.1) p (V p) = 0 := by
  classical
  obtain ⟨F, hF, Bf, hBf, hribbon⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_potentialPath_exists_uniform_compact_horizontalField
      I hφ hc hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨A₀, R₀, hA₀, _hR₀, hboundary⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_potentialPath_rounded_boundary_lifts
      I hφ hc hlower hupper hEnd hhom hL hend
  refine ⟨F, hF, ?_⟩
  intro D hFD
  have hD : 0 < D := hF.trans hFD
  let Bq : ℝ := max 1 (max (Real.log R₀) (4 * A₀ / D ^ 2))
  refine ⟨max Bf Bq, hBf.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβq : Bq ≤ β := (le_max_right _ _).trans hβ
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβq
  have hR : R₀ ≤ Real.exp β := by
    have hlog : Real.log R₀ ≤ β :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hβq)
    exact (Real.le_exp_log R₀).trans (Real.exp_le_exp.mpr hlog)
  have hA : 2 * A₀ ≤ D ^ 2 * β ^ 2 / 2 := by
    have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
    have hquot : 4 * A₀ / D ^ 2 ≤ β :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hβq)
    have hmul : 4 * A₀ ≤ β * D ^ 2 := (div_le_iff₀ hDsq).mp hquot
    have hsq : β ≤ β ^ 2 := by nlinarith
    nlinarith [mul_nonneg hDsq.le (sub_nonneg.mpr hsq)]
  obtain ⟨_Kstar, _hKstar, _hthreshold, hboundary⟩ := hboundary (Real.exp β) hR
  intro Aminus hAminus hgap
  obtain ⟨δ, hδ, hδgap, hboundary⟩ := hboundary (D ^ 2 * β ^ 2 / 2) hA Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd
  let R := Real.exp β
  let A := D ^ 2 * β ^ 2 / 2
  let τ : ℝ × LGSpace n → ℝ := Prod.fst
  let f : ℝ × LGSpace n → ℂ := fun p => W (I.alongCoefficientPath p.1) p.2
  let ψ : ℝ × LGSpace n → ℝ := fun p => potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1
  let q : ℝ × LGSpace n → ℝ := fun p => potentialPath_roundedDefiningFunction I φ R A m p
  let C : Set (ℝ × LGSpace n) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ q p ≤ 0}
  let Cr : Set (ℝ × LGSpace n) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ f p = (R : ℂ) ∧ ψ p ≤ Aminus}
  let Cb : Set (ℝ × LGSpace n) := C ∩ {p | q p = 0}
  let Cf : Set (ℝ × LGSpace n) := Cr ∩ {p | ψ p = Aminus}
  have hτ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ τ := by
    rw [modelWithCornersSelf_prod]; exact contMDiff_fst
  have hf : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f := by
    rw [modelWithCornersSelf_prod]; exact contMDiff_coefficientPath_W_native_joint I
  have hψ : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ψ := by
    exact contMDiff_potentialPath_value_joint hφ
  have hq : ContMDiff 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ q := by
    rw [modelWithCornersSelf_prod]; exact contMDiff_potentialPath_roundedDefiningFunction_joint I hφ R A m
  have hC : IsCompact C := isCompact_potentialPath_rounded_totalSpace I hφ hEnd1 hEnd
    hhom hc hlower hL hend R A (by dsimp [A]; positivity) m
  have hCr : IsCompact Cr := isCompact_potentialPath_truncatedTotalSpace
    I hφ hEnd1 hEnd hhom hc hlower hL hend R Aminus
      ((by positivity : (0 : ℝ) ≤ F ^ 2 * β ^ 2 / 2).trans hAminus)
  have hCb : IsCompact Cb := hC.inter_right (isClosed_eq hq.continuous continuous_const)
  have hCf : IsCompact Cf := hCr.inter_right (isClosed_eq hψ.continuous continuous_const)
  obtain ⟨Or, Bf, Vr, hOr, hCrOr, hBf, hCfBf, hVr, hrf, hrψ⟩ :=
    hribbon β ((le_max_left _ _).trans hβ) Aminus hAminus
  let Ubase : Set (ℝ × LGSpace n) :=
    {p | m.eps < (Complex.normSq (f p) - R ^ 2) - (ψ p - A)}
  have hUbase : IsOpen Ubase := isOpen_lt continuous_const
    (((Complex.continuous_normSq.comp hf.continuous).sub continuous_const).sub
      (hψ.continuous.sub continuous_const))
  have hCrbase : Cr ⊆ Ubase := by
    intro p hp
    change m.eps < (Complex.normSq (f p) - R ^ 2) - (ψ p - A)
    simp only [hp.2.1, Complex.normSq_ofReal, ← sq, sub_self, zero_sub]
    have := hp.2.2
    change δ < A - Aminus at hδgap
    linarith
  have hbase : ∀ p ∈ Ubase, q p = (Complex.normSq (f p) - R ^ 2) := by
    intro p hp
    have hle : ψ p - A ≤ (Complex.normSq (f p) - R ^ 2) := by
      change m.eps < (Complex.normSq (f p) - R ^ 2) - (ψ p - A) at hp
      linarith
    exact (m.profile.exact_away _ (by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      change m.eps ≤ -(ψ p - A - (Complex.normSq (f p) - R ^ 2))
      change m.eps < (Complex.normSq (f p) - R ^ 2) - (ψ p - A) at hp
      linarith)).trans (max_eq_right hle)
  obtain ⟨Br, hBr, hCrBr, hBrsub⟩ := normal_exists_closure_subset hCr.isClosed
    (hOr.inter hUbase) (fun p hp => ⟨hCrOr hp, hCrbase hp⟩)
  have hCfBrBf : Cf ⊆ Br ∩ Bf := by
    intro p hp
    exact ⟨hCrBr hp.1, hCfBf ⟨hp.1.1, hp.1.2.1, hp.2⟩⟩
  obtain ⟨Bfront, hBfront, hCfBfront, hBfrontsub⟩ := normal_exists_closure_subset
    hCf.isClosed (hBr.inter hBf) hCfBrBf
  have hboundary : ∀ a ∈ Cb, ∃ (P : Set (ℝ × LGSpace n))
      (Z : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
      IsOpen P ∧ a ∈ P ∧
      ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n)) (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
        (fun p => (⟨p, Z p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) P ∧
      ∀ p ∈ P, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℝ)
        (fun z => (τ z, q z)) p (Z p) = (1, 0) := by
    intro a ha
    exact (hboundary m hm hmd a.1 ha.1.1 a.2 ha.2).2
  choose W Z hW haW hZ heq using (fun a : Cb => hboundary a a.property)
  let Uq : Set (ℝ × LGSpace n) := ⋃ a : Cb, W a
  have hUq : IsOpen Uq := isOpen_iUnion hW
  have hCbUq : Cb ⊆ Uq := fun a ha => mem_iUnion_of_mem ⟨a, ha⟩ (haW ⟨a, ha⟩)
  obtain ⟨Bambient, hBambient, hCbBambient, hBambientsub⟩ :=
    normal_exists_closure_subset hCb.isClosed hUq hCbUq
  let S : Fin 4 → Set (ℝ × LGSpace n) := ![univ, closure Bambient, closure Br, closure Bfront]
  let L : Fin 4 → (p : ℝ × LGSpace n) →
      TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p →L[ℝ] ℝ × (ℂ × ℝ) := fun j p =>
    ![(mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod 0,
      (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
        ((0 : TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p →L[ℝ] ℂ).prod
          (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) q p)),
      (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
        ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) f p).prod 0),
      (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
        ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) f p).prod
          (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ψ p))] j
  have hlocal : ∀ a ∈ C, ∃ (P : Set (ℝ × LGSpace n))
      (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
      IsOpen P ∧ a ∈ P ∧
      ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n)) (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
        (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) P ∧
      ∀ j p, p ∈ P → p ∈ S j → L j p (V p) = (1, 0) := by
    intro a _ha
    by_cases har : a ∈ closure Br
    · refine ⟨Or ∩ Ubase, Vr, hOr.inter hUbase, hBrsub har,
        hVr.contMDiffOn.mono inter_subset_left, ?_⟩
      intro j p hp hs
      have hcomp := parameter_level_horizontal_components
        (hτ.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)) (Vr p) (hrf p hp.1)
      have hqr := potentialPath_rounded_derivative_zero_of_fiber_horizontal I φ R A m
        Ubase hUbase hbase p hp.2 (Vr p) (hrf p hp.1)
      fin_cases j
      · change (_, (0, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1]
      · change (_, (0, _)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1, hqr]
      · change (_, (_, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1, hcomp.2]
      · have hpBf := (hBfrontsub hs).2
        have hpψ := hrψ p ⟨hp.1, hpBf⟩
        change (_, (_, _)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ))
        erw [hcomp.1, hcomp.2, hpψ]
    · by_cases hab : a ∈ closure Bambient
      · obtain ⟨i, hai⟩ := mem_iUnion.mp (hBambientsub hab)
        refine ⟨W i ∩ (closure Br)ᶜ, Z i, (hW i).inter isClosed_closure.isOpen_compl,
          ⟨hai, har⟩, (hZ i).mono inter_subset_left, ?_⟩
        intro j p hp hs
        have hcomp := parameter_level_horizontal_components
          (hτ.mdifferentiableAt (by simp)) (hq.mdifferentiableAt (by simp)) (Z i p) (heq i p hp.1)
        fin_cases j
        · change (_, (0, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1]
        · change (_, (0, _)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1, hcomp.2]
        · exact False.elim (hp.2 hs)
        · exact False.elim (hp.2 (subset_closure (hBfrontsub hs).1))
      · obtain ⟨P, V, hP, haP, hV, hv⟩ := exists_parameter_level_horizontalField
          (E := Model (2 * n)) (F := Model 0) (M := LGSpace n) (a := a)
          (f := fun _ => 0) contMDiff_const (by
            intro z
            change Model 0 at z
            refine ⟨0, ?_⟩
            change _ = (z : Model 0)
            exact Subsingleton.elim _ _)
        refine ⟨P ∩ (closure Br)ᶜ ∩ (closure Bambient)ᶜ, V,
          (hP.inter isClosed_closure.isOpen_compl).inter isClosed_closure.isOpen_compl,
          ⟨⟨haP, har⟩, hab⟩, hV.mono (fun _ hp => hp.1.1), ?_⟩
        intro j p hp hs
        have hcomp := parameter_level_horizontal_components
          (hτ.mdifferentiableAt (by simp))
          (mdifferentiableAt_const (c := (0 : Model 0))) (V p) (hv p hp.1.1)
        fin_cases j
        · change (_, (0, 0)) = ((1 : ℝ), (0 : ℂ), (0 : ℝ)); erw [hcomp.1]
        · exact False.elim (hp.2 hs)
        · exact False.elim (hp.1.2 hs)
        · exact False.elim (hp.1.2 (subset_closure (hBfrontsub hs).1))
  obtain ⟨O, V, hO, hCO, hV, hL⟩ := exists_smooth_marked_affine_lift_near_compact
    C hC S L (fun _ _ => (1, 0)) hlocal
  refine ⟨O, Bambient, Br, Bfront, V, hO, hCO, hBambient, ?_, hBr, hCrBr,
    hBfront, ?_, hV, ?_, ?_, ?_, ?_⟩
  · intro p hp; exact hCbBambient ⟨⟨hp.1, hp.2.le⟩, hp.2⟩
  · intro p hp; exact hCfBfront ⟨⟨hp.1, hp.2.1, hp.2.2.le⟩, hp.2.2⟩
  · intro p hp; exact congrArg Prod.fst (hL 0 p hp (mem_univ _))
  · intro p hp
    exact congrArg (fun z : ℝ × (ℂ × ℝ) => z.2.2) (hL 1 p hp.1 (subset_closure hp.2))
  · intro p hp
    have hcomp := congrArg (fun z : ℝ × (ℂ × ℝ) => (z.1, z.2.1))
      (hL 2 p hp.1 (subset_closure hp.2))
    have hpair : HasMFDerivAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
        (fun z => (τ z, f z)) p
        ((mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) τ p).prod
          (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ) f p)) :=
      ⟨hτ.continuous.continuousAt.prodMk hf.continuous.continuousAt,
        (hτ.mdifferentiableAt (by simp)).hasMFDerivAt.2.prodMk
          (hf.mdifferentiableAt (by simp)).hasMFDerivAt.2⟩
    change mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ) (fun z => (τ z, f z)) p _ = _
    rw [hpair.mfderiv]
    exact hcomp
  · intro p hp
    exact congrArg (fun z : ℝ × (ℂ × ℝ) => z.2.2) (hL 3 p hp.1 (subset_closure hp.2))


end FsFltz.Geometry
