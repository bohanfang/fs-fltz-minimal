import FsFltz.Analysis.OriginalRoundingCorner
import FsFltz.Analysis.SmoothRoundingProfile
import FsFltz.Analysis.OriginalRatioBounds

/-!
# Existence of every admissible original rounding

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 878–908;
`geoemtric-part-fsf.tex`, `def:rounding`, lines 309–326, and `thm:target`,
lines 352–381. The native smooth-max constructor and proved corner-band
geometry produce an actual rounding choice for every admissible set of
parameters. The finite input produces all end and ratio-set bounds used in
the universal assertion. Domain/contact regularity, initial pairs and both
completion markings remain separate obligations of `prop:allinitial`.
-/

noncomputable section

namespace FsFltz.Geometry

variable {n : ℕ}

/-- Every valid original fiber bound and strict pair of truncation levels
admits an actual rounding at every `K` above the literal ratio-set threshold.
The conclusions are precisely the native `def:rounding` conditions, including
the actual manifold derivatives and corner covectors. -/
theorem exists_original_admissible_rounding (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (hA : Aminus < A) :
    ∃ m : RoundingChoice, GeometricAdmissibleRounding I R K Aminus A m := by
  obtain ⟨delta, hd, _, hround⟩ := exists_original_admissible_rounding_width I
    hamb hR hset hK hfib hlevels hA
  let m : RoundingChoice := ⟨delta, roundingProfile delta hd⟩
  exact ⟨m, hround m hd le_rfl⟩

end FsFltz.Geometry

namespace FsFltz

variable {n : ℕ}

/-- The finite toric input supplies one ambient end bound and one base
threshold for which the ratio set is well-defined, fiber end bounds exist,
and every valid fiber-bound/`K`/level choice admits an actual rounding.
This preserves the universal choices required by `thm:target`, target
lines 352–381, and proves the existence clause of `prop:allinitial`, proof
lines 878–908. No pair, marking, core, chain or grading is assumed. -/
theorem ToricInput.exists_initial_rounding_bounds (I : ToricInput n) :
    ∃ Aamb R0 : ℝ, AmbientEndBound I Aamb ∧
      max 1 (sublevelMagnitudeSup I Aamb) < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        RatioSetWellDefined I R ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb R Afib) ∧
        ∀ Afib : ℝ, FiberEndBound I Aamb R Afib →
          ∀ K : ℝ, K0 I R ≤ K →
            ∀ Aminus : ℝ, Afib < Aminus →
              ∀ A : ℝ, Aminus < A →
                ∃ m : RoundingChoice,
                  Geometry.GeometricAdmissibleRounding I R K Aminus A m := by
  obtain ⟨Aamb, R0, hamb, hR0, hbounds⟩ := I.exists_initial_analytic_bounds
  refine ⟨Aamb, R0, hamb, hR0, ?_⟩
  intro R hR
  obtain ⟨hne, hbdd, hfib⟩ := hbounds R hR
  refine ⟨⟨hne, hbdd⟩, hfib, ?_⟩
  intro Afib hAfib K hK Aminus hAminus A hA
  exact Geometry.exists_original_admissible_rounding I hamb (hR0.trans_le hR)
    ⟨hne, hbdd⟩ hK hAfib hAminus hA

end FsFltz
