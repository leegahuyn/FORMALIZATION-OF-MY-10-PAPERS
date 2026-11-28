import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCechHTwo
import PrimalitySheafVerification.ManuscriptAudit.InjectiveNativeCechPositive

/-! Exactness of all positive affine singleton Čech degrees propagates
to every successive injective cokernel and gives ordinary acyclicity. -/

namespace ManuscriptAudit.ProetaleAffineCechAcyclic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CechNerveLowDegrees (N)
open NativeCechNerve (Cech cochains)
open ProetaleAffineCechHTwo (AffineExactAt cokernel_sections_surjective)
open SingletonCoverRefinement (Covers)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev J (X : Scheme.{0}) := Scheme.ProEt.topology X
private abbrev C (X : Scheme.{0}) := Sheaf (J X) A

variable {X : Scheme.{0}}

local instance : EnoughInjectives (C X) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C X)

section Quotient

variable {F I : C X} (m : F ⟶ I) [Mono m]

private theorem presentation : (ShortComplex.cokernelSequence m).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact m)
    (inferInstanceAs (Mono m)) (inferInstanceAs (Epi (cokernel.π m)))

set_option maxHeartbeats 5800000 in
/-- The actual affine Čech complex of the quotient is exact in the
desired positive degree by exactness of its two neighboring terms. -/
theorem quotient_exactAt_succ (n : ℕ) (hF₁ : AffineExactAt X F 1)
    (hF₂ : AffineExactAt X F (n + 2))
    {U T : X.ProEt} (f : U ⟶ T) [IsAffine U.left] [IsAffine T.left]
    (hf : Covers (J X) f) (hI : (Cech f I.obj).ExactAt (n + 1)) :
    (Cech f (cokernel m).obj).ExactAt (n + 1) := by
  let S := ShortComplex.cokernelSequence m
  let B := sheafToPresheaf (J X) A ⋙ cochains f
  let P := S.map B
  have hP : P.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact P
    intro r
    let W := N f r
    let Q := P.map (HomologicalComplex.eval A (.up ℕ) r)
    letI : IsAffine W.left := ProetaleAffineCechTerms.isAffine_term f r
    have hExact : Q.Exact := (ShortComplex.ab_exact_iff_function_exact Q).mpr
      (SheafShortExactSections.sections_exact S (presentation m) W)
    have hMono : Mono Q.f := (AddCommGrpCat.mono_iff_injective _).mpr
      (SheafSectionDifference.section_injective m W)
    have hEpi : Epi Q.g := (AddCommGrpCat.epi_iff_surjective _).mpr
      (cokernel_sections_surjective m hF₁ W)
    exact ShortComplex.ShortExact.mk' hExact hMono hEpi
  change P.X₃.ExactAt (n + 1)
  apply (P.X₃.exactAt_iff_isZero_homology (n + 1)).mpr
  let e := hP.homology_exact₃ (n + 1) (n + 2)
    (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) by rfl)
  have hI' : IsZero (P.X₂.homology (n + 1)) := hI.isZero_homology
  have hF' : IsZero (P.X₁.homology (n + 2)) :=
    (hF₂ f inferInstance inferInstance hf).isZero_homology
  exact e.isZero_X₂ (hI'.eq_of_src _ _) (hF'.eq_of_tgt _ _)

variable [Injective I]

/-- Actual quotient by an injective preserves all the positive Čech conditions. -/
theorem quotient_exact_all (hF : ∀ n, AffineExactAt X F (n + 1)) (n : ℕ) :
    AffineExactAt X (cokernel m) (n + 1) := by
  intro U T f hU hT hf
  letI := hU
  letI := hT
  exact quotient_exactAt_succ m n (hF 0) (hF (n + 1)) f hf
    (InjectiveNativeCechPositive.exactAt_succ f I n)

end Quotient

variable [IsAffine X]

set_option maxHeartbeats 5800000 in
/-- All actual ordinary cohomology in positive degree vanishes. -/
theorem H_succ_subsingleton (F : C X)
    (hF : ∀ n, AffineExactAt X F (n + 1)) (d : ℕ) :
    Subsingleton (Sheaf.H F (d + 1)) := by
  induction d generalizing F with
  | zero =>
      let T := Scheme.ProEt.mk (𝟙 X)
      let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
      letI : IsAffine T.left := inferInstanceAs (IsAffine X)
      let m := Injective.ι F
      exact SheafH1Descent.H1_subsingleton_of_global_lifts m hT
        (cokernel_sections_surjective m (hF 0) T)
  | succ n ih =>
      let m := Injective.ι F
      let S := ShortComplex.cokernelSequence m
      letI : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
      have hQ : Subsingleton (Sheaf.H (cokernel m) (n + 1)) :=
        ih (cokernel m) (quotient_exact_all m hF)
      exact SheafCohomologyDimensionShift.H_succ_subsingleton_of_injectiveMiddle S
        (presentation m) (n + 1) hQ

end
end ManuscriptAudit.ProetaleAffineCechAcyclic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineCechAcyclic.quotient_exactAt_succ,
      ``ManuscriptAudit.ProetaleAffineCechAcyclic.quotient_exact_all,
      ``ManuscriptAudit.ProetaleAffineCechAcyclic.H_succ_subsingleton] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
