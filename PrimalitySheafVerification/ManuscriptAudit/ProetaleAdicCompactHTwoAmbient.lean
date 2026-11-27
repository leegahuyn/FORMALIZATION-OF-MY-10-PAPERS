import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicOpenClosedHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedPairEpi

/-! Actual adic compact degree two for an open with one or two disjoint
algebraically closed rational boundary points embeds into ambient degree two.
Its image is the kernel of the boundary restriction on ambient degree two. -/

namespace ManuscriptAudit.ProetaleAdicCompactHTwoAmbient

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleAdicClosedPairSupport (boundary pairRestriction)
open OpenProetaleExtension (extensionByZero)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}}

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A
private abbrev integers (X : Scheme.{0}) :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private def supportEquiv (S : ShortComplex (C X)) (hS : S.ShortExact)
    (hBoundary : Subsingleton (Sheaf.H S.X₃ 1)) :
    Sheaf.H S.X₁ 2 ≃+ (Sheaf.H.map S.g 2).ker := by
  have h := Ext.covariant_sequence_exact₂' (integers X) hS 2
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  have hExact : Function.Exact (Sheaf.H.map S.f 2) (Sheaf.H.map S.g 2) := h
  let m : Sheaf.H S.X₁ 2 →+ (Sheaf.H.map S.g 2).ker :=
    (Sheaf.H.map S.f 2).codRestrict _ (fun x ↦ (hExact _).2 ⟨x, rfl⟩)
  refine AddEquiv.ofBijective m ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' : Sheaf.H.map S.f 2 x = Sheaf.H.map S.f 2 y :=
      congrArg (fun b : (Sheaf.H.map S.g 2).ker ↦ b.val) hxy
    apply sub_eq_zero.mp
    have hz : Sheaf.H.map S.f 2 (x - y) = 0 := by rw [map_sub, hxy', sub_self]
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ (integers X) hS (x - y) hz
      (show 1 + 1 = 2 by rfl)
    have hb₀ : b = 0 := hBoundary.elim b 0
    rw [hb₀, Ext.zero_comp] at hb
    exact hb.symm
  · intro z
    obtain ⟨x, hx⟩ := (hExact z.val).1 z.property
    exact ⟨x, Subtype.ext hx⟩

private theorem supportEquiv_apply_val (S : ShortComplex (C X)) (hS : S.ShortExact)
    (hBoundary : Subsingleton (Sheaf.H S.X₃ 1)) (x : Sheaf.H S.X₁ 2) :
    (supportEquiv S hS hBoundary x).val = Sheaf.H.map S.f 2 x := rfl

variable (L : Type) [Field L] [IsAlgClosed L]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private theorem closedHOne_subsingleton (i : Spec (CommRingCat.of L) ⟶ X) :
    Subsingleton (Sheaf.H (functionsOver ℤ_[ℓ] i) 1) := by
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton L
    (functions ℤ_[ℓ] (Spec (CommRingCat.of L))) 0
  exact ProetaleDirectImageHOne.directImage_HOne_subsingleton i _

private theorem pairHOne_subsingleton (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X) :
    Subsingleton (Sheaf.H (boundary i₀ i₁ ℓ) 1) := by
  let F₀ := functionsOver ℤ_[ℓ] i₀
  let F₁ := functionsOver ℤ_[ℓ] i₁
  let e := cohomologyIso (X := X) (biprod.isoProd F₀ F₁).symm 1
  let h₀ := closedHOne_subsingleton L ℓ i₀
  let h₁ := closedHOne_subsingleton L ℓ i₁
  let p : Sheaf.H (F₀ ⊞ F₁) 1 ≃+ Sheaf.H F₀ 1 × Sheaf.H F₁ 1 :=
    Ext.addEquivBiprod
  exact ⟨fun x y ↦ (e.trans p).injective (Prod.ext (h₀.elim _ _) (h₁.elim _ _))⟩

variable {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- The actual compact group with one boundary point identifies with the
kernel of the ordinary cohomology map to the continuous closed direct image. -/
def singleEquiv (i : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i]
    (hComplement : Set.range j = (Set.range i)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] Y)) 2 ≃+
      (Sheaf.H.map (diagonal ℤ_[ℓ] i) 2).ker :=
  let S := ProetaleAdicClosedRestrictionEpi.sequence i ℓ
  let hS := ProetaleAdicClosedRestrictionEpi.sequence_shortExact i ℓ
  let e := ProetaleAdicClosedSupportKernel.extensionKernelIso i j ℓ hComplement
  (cohomologyIso (X := X) e 2).trans (supportEquiv S hS (closedHOne_subsingleton L ℓ i))

theorem singleEquiv_apply_val (i : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i]
    (hComplement : Set.range j = (Set.range i)ᶜ)
    (x : Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] Y)) 2) :
    (singleEquiv L ℓ j i hComplement x).val =
      Sheaf.H.map (ProetaleClosedKernelLocalSupport.inc i ℤ_[ℓ]) 2
        (cohomologyIso (X := X)
          (ProetaleAdicClosedSupportKernel.extensionKernelIso i j ℓ hComplement) 2 x) := rfl

/-- The corresponding actual kernel description for two disjoint rational boundary points. -/
def pairEquiv (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X)
    [IsClosedImmersion i₀] [IsClosedImmersion i₁]
    (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁))
    (hComplement : Set.range j = (Set.range i₀ ∪ Set.range i₁)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] Y)) 2 ≃+
      (Sheaf.H.map (pairRestriction i₀ i₁ ℓ) 2).ker :=
  let S := ProetaleAdicClosedPairEpi.sequence i₀ i₁ ℓ
  let hS := ProetaleAdicClosedPairEpi.sequence_shortExact i₀ i₁ ℓ hDisjoint
  let e := ProetaleAdicClosedPairSupport.extensionKernelIso i₀ i₁ ℓ j hComplement
  (cohomologyIso (X := X) e 2).trans (supportEquiv S hS (pairHOne_subsingleton L ℓ i₀ i₁))

theorem pairEquiv_apply_val (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X)
    [IsClosedImmersion i₀] [IsClosedImmersion i₁]
    (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁))
    (hComplement : Set.range j = (Set.range i₀ ∪ Set.range i₁)ᶜ)
    (x : Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] Y)) 2) :
    (pairEquiv L ℓ j i₀ i₁ hDisjoint hComplement x).val =
      Sheaf.H.map (ProetaleAdicClosedPairSupport.inclusion i₀ i₁ ℓ) 2
        (cohomologyIso (X := X)
          (ProetaleAdicClosedPairSupport.extensionKernelIso i₀ i₁ ℓ j hComplement) 2 x) := rfl

end
end ManuscriptAudit.ProetaleAdicCompactHTwoAmbient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicCompactHTwoAmbient.singleEquiv,
      ``ManuscriptAudit.ProetaleAdicCompactHTwoAmbient.singleEquiv_apply_val,
      ``ManuscriptAudit.ProetaleAdicCompactHTwoAmbient.pairEquiv,
      ``ManuscriptAudit.ProetaleAdicCompactHTwoAmbient.pairEquiv_apply_val] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
