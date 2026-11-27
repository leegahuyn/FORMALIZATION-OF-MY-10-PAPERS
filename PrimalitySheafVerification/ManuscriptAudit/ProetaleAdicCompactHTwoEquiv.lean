import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactHTwoAmbient
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedImageHTwo

/-! Actual integral adic compact H² is ordinary H² when the complement
consists of one or two disjoint algebraically closed rational points. -/

namespace ManuscriptAudit.ProetaleAdicCompactHTwoEquiv

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleAdicClosedPairSupport (boundary pairRestriction)
open OpenProetaleExtension (extensionByZero)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleAdicClosedImageHTwo (HTwo_subsingleton)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private def fullKernelEquiv {U V : Type*} [AddGroup U] [AddGroup V]
    (f : U →+ V) (hV : Subsingleton V) : f.ker ≃+ U where
  toFun x := x.val
  invFun x := ⟨x, hV.elim _ _⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {X Y : Scheme.{0}} (K : Type) [Field K] [IsAlgClosed K]
  (ℓ : ℕ) [Fact ℓ.Prime]
  (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

private abbrev A := AddCommGrpCat.{1}

private theorem pairHTwo_subsingleton (i₀ i₁ : Spec (CommRingCat.of K) ⟶ X)
    [IsClosedImmersion i₀] [IsClosedImmersion i₁] :
    Subsingleton (Sheaf.H (boundary i₀ i₁ ℓ) 2) := by
  let F₀ := functionsOver ℤ_[ℓ] i₀
  let F₁ := functionsOver ℤ_[ℓ] i₁
  let e := cohomologyIso (X := X) (biprod.isoProd F₀ F₁).symm 2
  let h₀ := HTwo_subsingleton i₀ ℓ
  let h₁ := HTwo_subsingleton i₁ ℓ
  let p : Sheaf.H (F₀ ⊞ F₁) 2 ≃+ Sheaf.H F₀ 2 × Sheaf.H F₁ 2 :=
    Ext.addEquivBiprod
  exact ⟨fun x y ↦ (e.trans p).injective (Prod.ext (h₀.elim _ _) (h₁.elim _ _))⟩

/-- The actual support-to-ambient map is an isomorphism for one boundary point. -/
def singleEquiv (i : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion i]
    (hComplement : Set.range j = (Set.range i)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] Y)) 2 ≃+ Sheaf.H (functions ℤ_[ℓ] X) 2 :=
  (ProetaleAdicCompactHTwoAmbient.singleEquiv K ℓ j i hComplement).trans
    (fullKernelEquiv (Sheaf.H.map (diagonal ℤ_[ℓ] i) 2) (HTwo_subsingleton i ℓ))

/-- The actual support-to-ambient map is an isomorphism for two disjoint boundary points. -/
def pairEquiv (i₀ i₁ : Spec (CommRingCat.of K) ⟶ X)
    [IsClosedImmersion i₀] [IsClosedImmersion i₁]
    (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁))
    (hComplement : Set.range j = (Set.range (i₀ : Spec (CommRingCat.of K) ⟶ X) ∪ Set.range i₁)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] Y)) 2 ≃+ Sheaf.H (functions ℤ_[ℓ] X) 2 :=
  (ProetaleAdicCompactHTwoAmbient.pairEquiv K ℓ j i₀ i₁ hDisjoint hComplement).trans
    (fullKernelEquiv (Sheaf.H.map (pairRestriction i₀ i₁ ℓ) 2)
      (pairHTwo_subsingleton K ℓ i₀ i₁))

end
end ManuscriptAudit.ProetaleAdicCompactHTwoEquiv

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicCompactHTwoEquiv.singleEquiv,
      ``ManuscriptAudit.ProetaleAdicCompactHTwoEquiv.pairEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
