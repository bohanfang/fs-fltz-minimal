import FsFltz.Analysis.OriginalFiberDomain
import FsFltz.Geometry.MarkedHorizontalFlow

/-!
# Actual transport between original full-ribbon levels

Source: `geometric-part-fsf-proof.tex`, `lem:choices`, lines 958–973,
especially the intrinsic exhaustion-band motion at lines 965–970;
`geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and `g:initial`,
lines 373–384. The actual full-fiber exhaustion constructs a supported
smooth horizontal flow. It transports the entire quadratic truncations,
including their boundaries, in both directions. Assembly of the compact
presentation maps and their completed pair deformation is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set Filter Function

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

variable {d : ℕ} (M : SmoothManifold d)

/-- The actual affine family of compact scalar sublevels has one smooth
horizontal field near its whole total space and an open boundary collar.
Only regularity on the level band is used; no motion or atlas is input. -/
theorem exists_affine_sublevel_horizontalField
    (η : M.Point → ℝ) (hη : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ η)
    (hcompact : ∀ B : ℝ, IsCompact {x | η x ≤ B}) (A B : ℝ)
    (hreg : ∀ x, min A B ≤ η x → η x ≤ max A B →
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) η x ≠ 0) :
    letI : ChartedSpace (ℝ × Model d) (ℝ × M.Point) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ (Model d)) (ℝ × M.Point))
    letI : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × M.Point) := by
      rw [modelWithCornersSelf_prod]
      exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞ (ℝ × M.Point))
    let ρ : ℝ × M.Point → ℝ := fun p => η p.2 - ((1 - p.1) * A + p.1 * B)
    ∃ (O T : Set (ℝ × M.Point))
      (V : (p : ℝ × M.Point) → TangentSpace 𝓘(ℝ, ℝ × Model d) p),
      IsOpen O ∧ {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ ρ p ≤ 0} ⊆ O ∧
      IsOpen T ∧ {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ ρ p = 0} ⊆ T ∧
      ContMDiff 𝓘(ℝ, ℝ × Model d) (𝓘(ℝ, ℝ × Model d)).tangent ∞
        (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model d) (ℝ × M.Point))) ∧
      (∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) Prod.fst p (V p) = (1 : ℝ)) ∧
      ∀ p ∈ O ∩ T, mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ρ p (V p) = 0 := by
  let : ChartedSpace (ℝ × Model d) (ℝ × M.Point) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model d)) (ℝ × M.Point))
  let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × M.Point) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞ (ℝ × M.Point))
  let : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model d) M.Point
  let : SigmaCompactSpace M.Point := sigmaCompactSpace_of_locallyCompact_secondCountable
  let ρ : ℝ × M.Point → ℝ := fun p => η p.2 - ((1 - p.1) * A + p.1 * B)
  have hτ : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × M.Point → ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hρ : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ∞ ρ := by
    rw [modelWithCornersSelf_prod]
    exact (hη.comp contMDiff_snd).sub
      (((contMDiff_const.sub contMDiff_fst).mul contMDiff_const).add
        (contMDiff_fst.mul contMDiff_const))
  have hlevel (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      min A B ≤ (1 - s) * A + s * B ∧ (1 - s) * A + s * B ≤ max A B := by
    have hs0 := hs.1
    have hs1 := hs.2
    constructor
    · calc
        min A B = (1 - s) * min A B + s * min A B := by ring
        _ ≤ (1 - s) * A + s * B := by gcongr <;> simp
    · calc
        (1 - s) * A + s * B ≤ (1 - s) * max A B + s * max A B := by
          gcongr <;> simp
        _ = max A B := by ring
  let C : Set (ℝ × M.Point) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ ρ p ≤ 0}
  let S : Set (ℝ × M.Point) := {p | ρ p = 0}
  have hC : IsCompact C := by
    apply (isCompact_Icc.prod (hcompact (max A B))).of_isClosed_subset
    · exact (isClosed_Icc.preimage hτ.continuous).inter
        (isClosed_le hρ.continuous continuous_const)
    · intro p hp
      exact ⟨hp.1, (sub_nonpos.mp hp.2).trans (hlevel p.1 hp.1).2⟩
  have hS : IsClosed S := isClosed_eq hρ.continuous continuous_const
  let D : (p : ℝ × M.Point) → TangentSpace 𝓘(ℝ, ℝ × Model d) p →L[ℝ] ℝ :=
    fun p => mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) Prod.fst p
  let H : (p : ℝ × M.Point) → TangentSpace 𝓘(ℝ, ℝ × Model d) p →L[ℝ] ℝ :=
    fun p => mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ρ p
  obtain ⟨O, T, V, hO, hCO, hT, hCT, hV, hD, hH⟩ :=
    exists_smooth_boundary_horizontal_lift_near_compact C hC S hS D H
      (fun _ => 1) (fun _ => 0) (by
        intro p _hp
        have hzero : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d))
            𝓘(ℝ, Model 0) ∞ (fun _ : ℝ × M.Point => (0 : Model 0)) := contMDiff_const
        obtain ⟨P, Z, hP, hpP, hZ, heq⟩ :=
          exists_parameter_level_horizontalField hzero (a := p)
            (fun y => by
              change Model 0 at y
              refine ⟨0, ?_⟩
              change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model 0)
                (fun _ : M.Point => (0 : Model 0)) p.2 (0 : Model d) : Model 0) = y
              exact @Subsingleton.elim (Model 0) inferInstance _ _)
        refine ⟨P, Z, hP, hpP, hZ, ?_⟩
        intro q hq
        have he := heq q hq
        have h₁ := (hτ.mdifferentiableAt (x := q) (by simp)).hasMFDerivAt
        have h₂ := (mdifferentiableAt_const (I := 𝓘(ℝ, ℝ × Model d))
          (I' := 𝓘(ℝ, Model 0)) (c := (0 : Model 0)) (x := q)).hasMFDerivAt
        have hj : HasMFDerivAt 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model 0)
            (fun q : ℝ × M.Point => (q.1, (0 : Model 0))) q
            ((mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) Prod.fst q).prod
              (mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, Model 0) (fun _ => (0 : Model 0)) q)) :=
          ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩
        rw [hj.mfderiv] at he
        exact congrArg Prod.fst he) (by
        intro p hp
        have hpη : η p.2 = (1 - p.1) * A + p.1 * B := sub_eq_zero.mp hp.2
        have hd : mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun x => ρ (p.1, x)) p.2 =
            mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) η p.2 := by
          change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ)
            (η - fun _ => ((1 - p.1) * A + p.1 * B)) p.2 : Model d →L[ℝ] ℝ) = _
          rw [mfderiv_sub (hη.mdifferentiableAt (by simp)) mdifferentiableAt_const,
            mfderiv_const, sub_zero]
        have hne := hreg p.2 (hpη ▸ (hlevel p.1 hp.1.1).1)
          (hpη ▸ (hlevel p.1 hp.1.1).2)
        have hsurj : Function.Surjective
            (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun x => ρ (p.1, x)) p.2) := by
          rw [hd]
          apply LinearMap.surjective (f :=
            (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) η p.2 : Model d →L[ℝ] ℝ).toLinearMap)
          intro he
          exact hne (ContinuousLinearMap.coe_injective he)
        have hρ' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ ρ := by
          simpa only [modelWithCornersSelf_prod] using hρ
        obtain ⟨P, Z, hP, hpP, hZ, heq⟩ := exists_parameter_level_horizontalField hρ' hsurj
        refine ⟨P, Z, hP, hpP, hZ, ?_⟩
        intro q hq
        have he := heq q hq
        have h₁ := (hτ.mdifferentiableAt (x := q) (by simp)).hasMFDerivAt
        have h₂ := (hρ.mdifferentiableAt (x := q) (by simp)).hasMFDerivAt
        have hj : HasMFDerivAt 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × ℝ)
            (fun q : ℝ × M.Point => (q.1, ρ q)) q
            ((mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) Prod.fst q).prod
              (mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ρ q)) :=
          ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩
        rw [hj.mfderiv] at he
        exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩)
  exact ⟨O, T, V, hO, hCO, hT,
    fun p hp => hCT ⟨⟨hp.1, hp.2.le⟩, hp.2⟩, hV, hD, hH⟩

/-- The actual affine sublevel family has jointly smooth complete motion
transporting every compact sublevel and its boundary in either direction.
The flow is constructed by a supported cutoff of the proved horizontal
field; confinement follows from the original scalar equation. -/
theorem exists_affine_sublevel_transport
    (η : M.Point → ℝ) (hη : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ η)
    (hcompact : ∀ B : ℝ, IsCompact {x | η x ≤ B}) (A B : ℝ)
    (hreg : ∀ x, min A B ≤ η x → η x ≤ max A B →
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) η x ≠ 0) :
    letI : ChartedSpace (ℝ × Model d) (ℝ × M.Point) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ (Model d)) (ℝ × M.Point))
    letI : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × M.Point) := by
      rw [modelWithCornersSelf_prod]
      exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞ (ℝ × M.Point))
    ∃ Φ : Flow ℝ (ℝ × M.Point),
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model d)) 𝓘(ℝ, ℝ × Model d) ∞
        (fun p : ℝ × (ℝ × M.Point) => Φ p.1 p.2) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, η x ≤ (1 - s) * A + s * B →
        ∀ t : ℝ, s + t ∈ Icc (0 : ℝ) 1 →
          (Φ t (s, x)).1 = s + t ∧
          η (Φ t (s, x)).2 ≤ (1 - (s + t)) * A + (s + t) * B ∧
          (η x = (1 - s) * A + s * B →
            η (Φ t (s, x)).2 = (1 - (s + t)) * A + (s + t) * B) := by
  let : ChartedSpace (ℝ × Model d) (ℝ × M.Point) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model d)) (ℝ × M.Point))
  let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × M.Point) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞ (ℝ × M.Point))
  let ρ : ℝ × M.Point → ℝ := fun p => η p.2 - ((1 - p.1) * A + p.1 * B)
  have hτ : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × M.Point → ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hρ : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ∞ ρ := by
    rw [modelWithCornersSelf_prod]
    exact (hη.comp contMDiff_snd).sub
      (((contMDiff_const.sub contMDiff_fst).mul contMDiff_const).add
        (contMDiff_fst.mul contMDiff_const))
  have hC : IsCompact {p : ℝ × M.Point | p.1 ∈ Icc (0 : ℝ) 1 ∧ ρ p ≤ 0} := by
    apply (isCompact_Icc.prod (hcompact (max A B))).of_isClosed_subset
    · exact (isClosed_Icc.preimage hτ.continuous).inter
        (isClosed_le hρ.continuous continuous_const)
    · intro p hp
      refine ⟨hp.1, (sub_nonpos.mp hp.2).trans ?_⟩
      have hs0 := hp.1.1
      have hs1 := hp.1.2
      calc
        (1 - p.1) * A + p.1 * B ≤ (1 - p.1) * max A B + p.1 * max A B := by
          gcongr <;> simp
        _ = max A B := by ring
  obtain ⟨O, T, V, hO, hCO, hT, hCT, hV, hD, hH⟩ :=
    M.exists_affine_sublevel_horizontalField η hη hcompact A B hreg
  obtain ⟨P, K, W, Φ, hP, hCP, hPO, _hK, _hW, _hzero, heq, hΦ, hode⟩ :=
    exists_supported_horizontalFlow_near_compact hC hO hCO V hV.contMDiffOn
  have hder : ∀ p ∈ P, mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model 0)
      (fun q : ℝ × M.Point => (q.1, (0 : Model 0))) p (W p) = (1, 0) := by
    intro p hp
    have h₁ := (hτ.mdifferentiableAt (x := p) (by simp)).hasMFDerivAt
    have h₂ := (mdifferentiableAt_const (I := 𝓘(ℝ, ℝ × Model d))
      (I' := 𝓘(ℝ, Model 0)) (c := (0 : Model 0)) (x := p)).hasMFDerivAt
    have hj : HasMFDerivAt 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model 0)
        (fun q : ℝ × M.Point => (q.1, (0 : Model 0))) p
        ((mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) Prod.fst p).prod
          (mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, Model 0) (fun _ => (0 : Model 0)) p)) :=
      ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩
    rw [hj.mfderiv, mfderiv_const]
    apply Prod.ext
    · change mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) Prod.fst p (W p) = (1 : ℝ)
      rw [heq p hp]
      exact hD p (hPO hp)
    · rfl
  have hpot : ∀ p ∈ P ∩ T, mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ) ρ p (W p) = 0 := by
    intro p hp
    rw [heq p hp.1]
    exact hH p ⟨hPO hp.1, hp.2⟩
  have hpres := horizontalFlow_preserves_parameter_truncation Prod.fst ρ
    (fun _ : ℝ × M.Point => (0 : Model 0)) hτ hρ contMDiff_const 0 0 P T hP hT
    (fun p hp => hCP ⟨hp.1, hp.2.2⟩) (fun p hp => hCT ⟨hp.1, hp.2.2⟩)
    W Φ hode hder hpot
  refine ⟨Φ, hΦ, ?_⟩
  intro s hs x hx t ht
  obtain ⟨hparam, _hf, hsub, hboundary⟩ :=
    hpres (s, x) hs rfl (sub_nonpos.mpr hx) t ht
  refine ⟨hparam, ?_, ?_⟩
  · change η (Φ t (s, x)).2 - ((1 - (Φ t (s, x)).1) * A + (Φ t (s, x)).1 * B) ≤ 0 at hsub
    rw [hparam] at hsub
    exact sub_nonpos.mp hsub
  · intro hxb
    have he := hboundary (sub_eq_zero.mpr hxb)
    change η (Φ t (s, x)).2 - ((1 - (Φ t (s, x)).1) * A + (Φ t (s, x)).1 * B) = 0 at he
    rw [hparam] at he
    exact sub_eq_zero.mp he

/-- Two-direction confinement and the flow group law give literal images
of the entire compact sublevels and boundary levels under spatial motion. -/
theorem affine_sublevel_transport_images
    (η : M.Point → ℝ) (A B : ℝ) (Φ : Flow ℝ (ℝ × M.Point))
    (hpres : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, η x ≤ (1 - s) * A + s * B →
      ∀ t : ℝ, s + t ∈ Icc (0 : ℝ) 1 →
        (Φ t (s, x)).1 = s + t ∧
        η (Φ t (s, x)).2 ≤ (1 - (s + t)) * A + (s + t) * B ∧
        (η x = (1 - s) * A + s * B →
          η (Φ t (s, x)).2 = (1 - (s + t)) * A + (s + t) * B))
    {s u : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    (fun x => (Φ (u - s) (s, x)).2) '' {x | η x ≤ (1 - s) * A + s * B} =
        {x | η x ≤ (1 - u) * A + u * B} ∧
    (fun x => (Φ (u - s) (s, x)).2) '' {x | η x = (1 - s) * A + s * B} =
        {x | η x = (1 - u) * A + u * B} := by
  have hforward (x : M.Point) (hx : η x ≤ (1 - s) * A + s * B) :
      (Φ (u - s) (s, x)).1 = u ∧
      η (Φ (u - s) (s, x)).2 ≤ (1 - u) * A + u * B ∧
      (η x = (1 - s) * A + s * B → η (Φ (u - s) (s, x)).2 = (1 - u) * A + u * B) := by
    simpa only [show s + (u - s) = u by ring] using
      hpres s hs x hx (u - s) (by simpa only [show s + (u - s) = u by ring] using hu)
  have hreverse (x : M.Point) (hx : η x ≤ (1 - u) * A + u * B) :
      (Φ (s - u) (u, x)).1 = s ∧
      η (Φ (s - u) (u, x)).2 ≤ (1 - s) * A + s * B ∧
      (η x = (1 - u) * A + u * B → η (Φ (s - u) (u, x)).2 = (1 - s) * A + s * B) := by
    simpa only [show u + (s - u) = s by ring] using
      hpres u hu x hx (s - u) (by simpa only [show u + (s - u) = s by ring] using hs)
  have hround (x : M.Point) (hx : η x ≤ (1 - u) * A + u * B) :
      (Φ (u - s) (s, (Φ (s - u) (u, x)).2)).2 = x := by
    have hp : (s, (Φ (s - u) (u, x)).2) = Φ (s - u) (u, x) :=
      Prod.ext (hreverse x hx).1.symm rfl
    rw [hp, ← Φ.map_add, show (u - s) + (s - u) = 0 by ring, Φ.map_zero_apply]
  constructor
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hforward y hy).2.1
    · intro hx
      exact ⟨(Φ (s - u) (u, x)).2, (hreverse x hx).2.1, hround x hx⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hforward y hy.le).2.2 hy
    · intro hx
      exact ⟨(Φ (s - u) (u, x)).2, (hreverse x hx.le).2.2 hx, hround x hx.le⟩

end SmoothManifold

section Original

variable {n : ℕ} (I : ToricInput n) {Aamb R Afib : ℝ}
  (hamb : AmbientEndBound I Aamb)
  (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
  (hfib : FiberEndBound I Aamb R Afib)
  {A B : ℝ} (hA : Afib < A) (hB : Afib < B)

local notation "F" => originalFullFiberModel I hamb hR
local notation "η" => (phi0 ∘ SmoothEmbedding.map
  (FullFiberModel.embedding (originalFullFiberModel I hamb hR)))

include hfib hA hB in

/-- Every two original admissible ribbon levels have actual jointly smooth
motion of their whole compact truncations and native boundaries, throughout
the affine level interval. Positivity is proved on the original full-fiber
model; rank one is included without a nonempty boundary assumption. -/
theorem exists_originalRibbonLevel_transport :
    letI : ChartedSpace (ℝ × Model (2 * n - 2)) (ℝ × (F).ambient.manifold.Point) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n - 2)))
        (ℝ × (F).ambient.manifold.Point))
    letI : IsManifold 𝓘(ℝ, ℝ × Model (2 * n - 2)) ∞ (ℝ × (F).ambient.manifold.Point) := by
      rw [modelWithCornersSelf_prod]
      exact inferInstanceAs (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n - 2))) ∞
        (ℝ × (F).ambient.manifold.Point))
    ∃ Φ : Flow ℝ (ℝ × (F).ambient.manifold.Point),
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n - 2)))
        𝓘(ℝ, ℝ × Model (2 * n - 2)) ∞
        (fun p : ℝ × (ℝ × (F).ambient.manifold.Point) => Φ p.1 p.2) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, η x ≤ (1 - s) * A + s * B →
        ∀ t : ℝ, s + t ∈ Icc (0 : ℝ) 1 →
          (Φ t (s, x)).1 = s + t ∧
          η (Φ t (s, x)).2 ≤ (1 - (s + t)) * A + (s + t) * B ∧
          (η x = (1 - s) * A + s * B →
            η (Φ t (s, x)).2 = (1 - (s + t)) * A + (s + t) * B) := by
  apply (F).ambient.manifold.exists_affine_sublevel_transport η
    (contMDiff_originalFullFiber_phi0 I hamb hR)
    (isCompact_originalFullFiber_phi0_sublevel_all I hamb hR) A B
  intro x hx _hupper he
  have hp := scalarDerivative_originalFullFiber_phi0_pos I hamb hR hfib x
    ((lt_min hA hB).le.trans hx)
  unfold scalarDerivative at hp
  rw [he] at hp
  exact (lt_irrefl 0) hp

include hfib hA hB in
/-- The constructed original motion maps the entire compact ribbon to the
literal prescribed `InitialRibbon` at every intermediate target level.
It simultaneously gives equality of native boundary-level images. -/
theorem exists_originalRibbonLevel_transport_images :
    letI : ChartedSpace (ℝ × Model (2 * n - 2)) (ℝ × (F).ambient.manifold.Point) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n - 2)))
        (ℝ × (F).ambient.manifold.Point))
    ∃ Φ : Flow ℝ (ℝ × (F).ambient.manifold.Point),
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n - 2)))
        𝓘(ℝ, ℝ × Model (2 * n - 2)) ∞
        (fun p : ℝ × (ℝ × (F).ambient.manifold.Point) => Φ p.1 p.2) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        (fun x => (F).embedding.map (Φ (u - s) (s, x)).2) ''
            {x | η x ≤ (1 - s) * A + s * B} = InitialRibbon I R ((1 - u) * A + u * B) ∧
        (fun x => (Φ (u - s) (s, x)).2) '' {x | η x = (1 - s) * A + s * B} =
            {x | η x = (1 - u) * A + u * B} := by
  obtain ⟨Φ, hΦ, hpres⟩ := exists_originalRibbonLevel_transport I hamb hR hfib hA hB
  refine ⟨Φ, hΦ, ?_⟩
  intro s hs u hu
  obtain ⟨hsub, hboundary⟩ :=
    (F).ambient.manifold.affine_sublevel_transport_images η A B Φ hpres hs hu
  refine ⟨?_, hboundary⟩
  rw [show (fun x => (F).embedding.map (Φ (u - s) (s, x)).2) =
    (F).embedding.map ∘ (fun x => (Φ (u - s) (s, x)).2) from rfl, image_comp, hsub]
  have hlevel : Afib < (1 - u) * A + u * B := by
    have hmin : min A B ≤ (1 - u) * A + u * B := by
      have hu0 := hu.1
      have hu1 := hu.2
      calc
        min A B = (1 - u) * min A B + u * min A B := by ring
        _ ≤ (1 - u) * A + u * B := by gcongr <;> simp
    exact (lt_min hA hB).trans_le hmin
  rw [← originalFiberLiouvilleDomain_carrier I hamb hR hfib hlevel]
  exact originalFiberLiouvilleDomain_image I hamb hR hfib hlevel

end Original
end FsFltz.Geometry
