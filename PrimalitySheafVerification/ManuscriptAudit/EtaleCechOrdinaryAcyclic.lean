import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CochainQuotientExact
import PrimalitySheafVerification.ManuscriptAudit.EtaleCechSectionLifts
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyPositiveShift
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections

/-! Ordinary affine étale acyclicity from singleton Čech acyclicity
and Čech-acyclic injective presentations. -/

namespace ManuscriptAudit.EtaleCechOrdinaryAcyclic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleCechDirectSum EtaleCechSectionLifts

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} [HasFiniteLimits S.AffineEtale]

private abbrev J := Scheme.AffineEtale.topology S
private abbrev Ab := AddCommGrpCat.{0}
private abbrev C := Sheaf (J (S := S)) Ab

variable [(J (S := S)).HasSheafCompose (forget Ab)]
variable [(J (S := S)).WEqualsLocallyBijective Ab]
variable [HasExt.{0} (C (S := S))]

private abbrev sheafCochains {U T : S.AffineEtale} (f : U ⟶ T) :
    C (S := S) ⥤ CochainComplex Ab ℕ :=
  sheafToPresheaf (J (S := S)) Ab ⋙ cochains f

private instance {U T : S.AffineEtale} (f : U ⟶ T) :
    (sheafCochains f).PreservesZeroMorphisms where
  map_zero X Y := by
    ext n
    rfl

private theorem cokernelSequence_shortExact {A B : C (S := S)} (i : A ⟶ B) [Mono i] :
    (ShortComplex.cokernelSequence i).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i)
    (inferInstanceAs (Mono i)) (inferInstanceAs (Epi (cokernel.π i)))

/-- If the kernel and middle sheaves are singleton Čech-acyclic,
then the genuine sheaf cokernel is as well. -/
theorem affine_cokernel_cechAcyclic {A B : C (S := S)}
    (i : A ⟶ B) [Mono i] (hA : AffineCechAcyclic A) (hB : AffineCechAcyclic B) :
    AffineCechAcyclic (cokernel i) := by
  intro U T f hf n
  let S₀ := ShortComplex.cokernelSequence i
  let S₁ := S₀.map (sheafCochains f)
  have hS₀ : S₀.ShortExact := cokernelSequence_shortExact i
  have hPoint (k : ℕ) :
      (S₁.map (HomologicalComplex.eval Ab (.up ℕ) k)).ShortExact := by
    let W := CechNerveLowDegrees.N f k
    let C₀ := S₁.map (HomologicalComplex.eval Ab (.up ℕ) k)
    change C₀.ShortExact
    have hExact : C₀.Exact := ShortComplex.ab_exact_iff_function_exact.mpr
      (SheafShortExactSections.sections_exact S₀ hS₀ W)
    have hMono : Mono C₀.f := (AddCommGrpCat.mono_iff_injective _).mpr
      (SheafSectionDifference.section_injective i W)
    have hEpi : Epi C₀.g := (AddCommGrpCat.epi_iff_surjective _).mpr
      (affine_cokernel_sections_surjective hA i W)
    exact ShortComplex.ShortExact.mk' hExact hMono hEpi
  exact CochainQuotientExact.quotient_exactAt_succ S₁ n hPoint (hA f hf (n + 1)) (hB f hf n)

/-- Singleton Čech-acyclic sheaves have zero positive ordinary affine
étale cohomology when they admit Čech-acyclic injective presentations. -/
theorem affine_H_succ_subsingleton {T : S.AffineEtale} (hT : IsTerminal T)
    (hI : ∀ A : C (S := S), AffineCechAcyclic A →
      ∃ I : InjectivePresentation A, AffineCechAcyclic I.J)
    (n : ℕ) (A : C (S := S)) (hA : AffineCechAcyclic A) :
    Subsingleton (Sheaf.H A (n + 1)) := by
  induction n generalizing A with
  | zero =>
    obtain ⟨I, _⟩ := hI A hA
    exact affine_HOne_subsingleton hA I.f hT
  | succ n ih =>
    obtain ⟨I, hIJ⟩ := hI A hA
    let S₀ := ShortComplex.cokernelSequence I.f
    have hS₀ : S₀.ShortExact := cokernelSequence_shortExact I.f
    letI : Injective S₀.X₂ := I.injective
    exact SheafCohomologyDimensionShift.H_succ_subsingleton_of_injectiveMiddle S₀ hS₀
      (n + 1) (ih (cokernel I.f) (affine_cokernel_cechAcyclic I.f hA hIJ))

end

end ManuscriptAudit.EtaleCechOrdinaryAcyclic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleCechOrdinaryAcyclic.affine_cokernel_cechAcyclic,
      ``ManuscriptAudit.EtaleCechOrdinaryAcyclic.affine_H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
