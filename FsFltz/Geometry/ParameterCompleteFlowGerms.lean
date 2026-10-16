import FsFltz.Geometry.FamilyLiouvilleLocalFlow

/-!
# Real-open germs of actual parameterwise complete flows

Source: `geoemtric-part-fsf.tex`, smoothness convention, lines 119–122;
`def:pair`, lines 153–158; `def:chain`, lines 163–189; and `sec:lean`,
lines 788–814. An ordinary smooth extension of the family field near a
compact finite orbit segment produces a real-open germ of the actual
interval flows. A compact cutoff gives a smooth auxiliary action; uniqueness
and a compact tube identify it with the supplied slice curves. Completeness
and field equations are required only on the retained interval parameters.
The auxiliary flow has no source geometric significance outside that base.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function

namespace FsFltz.Geometry.CollarFlow

variable {E H Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [CompleteSpace E] [FiniteDimensional ℝ E] [LocallyCompactSpace H]
  [T2Space Q] [SecondCountableTopology Q]

set_option backward.isDefEq.respectTransparency false in
/-- A smooth family field on an ordinary real-open neighborhood of a compact
center orbit segment yields a real-open germ of the actual complete flows.
The matching equation and all original field laws are used only for `s ∈ S`.
The margin `|r₀| < R` includes positive and negative finite flow times. -/
theorem exists_parameterCompleteFlow_realGerm
    (S : Set Parameter) (ζ : Parameter → (x : Q) → TangentSpace I x)
    (hζ : ∀ s ∈ S, ContMDiff I I.tangent ∞
      (fun x => (⟨x, ζ s x⟩ : TangentBundle I Q)))
    (Φ : Parameter → ℝ → Q → Q)
    (hself : ∀ s ∈ S, ∀ x, Φ s 0 x = x)
    (hΦ : ∀ s ∈ S, ∀ x, IsMIntegralCurve (fun r => Φ s r x) (ζ s))
    (Z : ℝ → (x : Q) → TangentSpace I x)
    {Ω : Set (ℝ × Q)} (hΩ : IsOpen Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle I Q)) Ω)
    (hext : ∀ s ∈ S, ∀ x, (s.val, x) ∈ Ω → Z s.val x = ζ s x)
    (s₀ : Parameter) (hs₀ : s₀ ∈ S) (r₀ : ℝ) (x₀ : Q) (R : ℝ)
    (hR : |r₀| < R)
    (horbit : ∀ r ∈ Icc (-R) R, (s₀.val, Φ s₀ r x₀) ∈ Ω) :
    ∃ U : Set (ℝ × (ℝ × Q)), IsOpen U ∧ (s₀.val, (r₀, x₀)) ∈ U ∧
      ∃ β : ℝ × (ℝ × Q) → Q,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) I ∞ β U ∧
        ∀ s ∈ S, ∀ r x, (s.val, (r, x)) ∈ U → β (s.val, (r, x)) = Φ s r x := by
  let : LocallyCompactSpace (ModelProd ℝ H) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × H))
  have hRpos : 0 < R := (abs_nonneg r₀).trans_lt hR
  let γ : ℝ → ℝ × Q := fun r => (s₀.val, Φ s₀ r x₀)
  let K : Set (ℝ × Q) := γ '' Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.image
    (continuous_const.prodMk (hΦ s₀ hs₀ x₀).continuous)
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨r, hr, rfl⟩
    exact horbit r hr
  let v : (p : ℝ × Q) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) p :=
    fun p => constantParameterLift (Z p.1) p
  have hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p => (⟨p, v p⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) Ω := by
    have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
        (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
      ((ht.comp contMDiff_fst).contMDiffOn.prodMk hZ)
  obtain ⟨χ, V, hχ, hKV, hone, hsupport, hsuppΩ⟩ :=
    CollarExtension.exists_smooth_compact_cutoff
      (I := (𝓘(ℝ, ℝ)).prod I) hK hΩ hKΩ
  let W : (p : ℝ × Q) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) p :=
    fun p => χ p • v p
  have hW : ContMDiff ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p => (⟨p, W p⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) :=
    hχ.contMDiffOn.smul_section_of_tsupport hΩ hsuppΩ hv
  obtain ⟨F, hF, hode⟩ := exists_supported_smoothFlow W hW hsupport
    (fun p hp => by simp only [W, image_eq_zero_of_notMem_tsupport hp, zero_smul])
  have hfst : ∀ r p, (F r p).1 = p.1 := by
    intro r p
    have hd : ∀ u : ℝ, HasDerivAt (fun a => (F a p).1) (0 : ℝ) u := by
      intro u
      have hm := (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (F u p)).comp u (hode p u)
      have hh := (hasMFDerivAt_iff_hasFDerivAt.mp hm).hasDerivAt
      apply hh.congr_deriv
      change (1 : ℝ) • (χ (F u p) • (0 : ℝ)) = 0
      simp only [smul_zero]
    have he : (fun a => (F a p).1) = fun _ => p.1 := by
      apply ODE_solution_unique_univ (t₀ := 0) (v := fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
        (s := fun _ => univ) (K := 0) (fun _ => (LipschitzWith.const 0).lipschitzOnWith)
      · exact fun u => ⟨hd u, mem_univ _⟩
      · exact fun u => ⟨hasDerivAt_const u _, mem_univ _⟩
      · exact congrArg Prod.fst (F.map_zero_apply p)
    exact congrFun he r
  have hγ : IsMIntegralCurveOn γ W (Ioo (-R) R) := by
    intro r hr
    have hmem : γ r ∈ K := ⟨r, Ioo_subset_Icc_self hr, rfl⟩
    have hd := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) s₀.val r).prodMk
      (hΦ s₀ hs₀ x₀ r)
    apply (hd.congr_mfderiv ?_).hasMFDerivWithinAt
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change ((0 : ℝ), a • ζ s₀ (Φ s₀ r x₀)) = a • W (γ r)
    simp only [W, v, constantParameterLift, hone _ (hKV hmem), one_smul]
    rw [hext s₀ hs₀ _ (hKΩ hmem)]
    exact Prod.ext (smul_zero a).symm rfl
  have hcenter : EqOn (fun r => F r (s₀.val, x₀)) γ (Ioo (-R) R) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (show (0 : ℝ) ∈ Ioo (-R) R by constructor <;> linarith)
      (hW.of_le (by simp)) ((hode _).isMIntegralCurveOn _) hγ (by
        simp only [Flow.map_zero_apply, γ, hself s₀ hs₀])
  let R' : ℝ := (|r₀| + R) / 2
  have hr₀ : |r₀| < R' := by dsimp only [R']; linarith
  have hR' : R' < R := by dsimp only [R']; linarith
  have hR'pos : 0 < R' := (abs_nonneg r₀).trans_lt hr₀
  let T : Set (ℝ × (ℝ × Q)) :=
    (fun p : ℝ × (ℝ × Q) => F p.1 p.2) ⁻¹' ((V : Set (ℝ × Q)) ∩ Ω)
  have hT : IsOpen T := (V.isOpen.inter hΩ).preimage hF.continuous
  have hseam : Icc (-R') R' ×ˢ ({(s₀.val, x₀)} : Set (ℝ × Q)) ⊆ T := by
    rintro ⟨r, p⟩ ⟨hr, hp⟩
    have hp' : p = (s₀.val, x₀) := hp
    subst p
    have hrR : r ∈ Ioo (-R) R := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hm : γ r ∈ K := ⟨r, Ioo_subset_Icc_self hrR, rfl⟩
    change F r (s₀.val, x₀) ∈ (V : Set (ℝ × Q)) ∩ Ω
    have he : F r (s₀.val, x₀) = γ r := hcenter hrR
    rw [he]
    exact ⟨hKV hm, hKΩ hm⟩
  obtain ⟨B, A, _, hA, hIB, hpA, hBA⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hT hseam
  have htube : ∀ p ∈ A, ∀ r ∈ Icc (-R') R', F r p ∈ (V : Set (ℝ × Q)) ∩ Ω := by
    intro p hp r hr
    exact hBA (show (r, p) ∈ B ×ˢ A from ⟨hIB hr, hp⟩)
  have heq : ∀ s ∈ S, ∀ x, (s.val, x) ∈ A →
      EqOn (fun r => (F r (s.val, x)).2) (fun r => Φ s r x) (Ioo (-R') R') := by
    intro s hs x hx
    have hc : IsMIntegralCurveOn (fun r => (F r (s.val, x)).2) (ζ s) (Ioo (-R') R') := by
      intro r hr
      have hmem := htube (s.val, x) hx r (Ioo_subset_Icc_self hr)
      have hd := (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I)
        (F r (s.val, x))).comp r (hode (s.val, x) r)
      apply (hd.congr_mfderiv ?_).hasMFDerivWithinAt
      apply ContinuousLinearMap.ext
      intro a
      change ℝ at a
      change a • (W (F r (s.val, x))).2 = a • ζ s (F r (s.val, x)).2
      simp only [W, v, constantParameterLift, hone _ hmem.1, one_smul, hfst]
      have hpair : (s.val, (F r (s.val, x)).2) = F r (s.val, x) :=
        Prod.ext (hfst r (s.val, x)).symm rfl
      rw [hext s hs _ (by rw [hpair]; exact hmem.2)]
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (show (0 : ℝ) ∈ Ioo (-R') R' by constructor <;> linarith)
      ((hζ s hs).of_le (by simp)) hc ((hΦ s hs x).isMIntegralCurveOn _) (by
        simp only [Flow.map_zero_apply, hself s hs])
  let U : Set (ℝ × (ℝ × Q)) :=
    (fun p : ℝ × (ℝ × Q) => (p.1, p.2.2)) ⁻¹' A ∩
      (fun p : ℝ × (ℝ × Q) => p.2.1) ⁻¹' Ioo (-R') R'
  have hU : IsOpen U :=
    (hA.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).inter
      (isOpen_Ioo.preimage (continuous_fst.comp continuous_snd))
  let β : ℝ × (ℝ × Q) → Q := fun p => (F p.2.1 (p.1, p.2.2)).2
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) I ∞ β :=
    contMDiff_snd.comp (hF.comp
      ((contMDiff_fst.comp contMDiff_snd).prodMk
        (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd))))
  refine ⟨U, hU, ⟨hpA (mem_singleton _), abs_lt.mp hr₀⟩, β, hβ.contMDiffOn, ?_⟩
  intro s hs r x hx
  exact heq s hs x hx.1 hx.2

end FsFltz.Geometry.CollarFlow
