import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedPairEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicBoundaryPairCoordinates
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! For two disjoint closed geometric points in a preconnected scheme, the
actual native support H¹ is an extension of ambient H¹ by the difference line. -/

namespace ManuscriptAudit.ProetaleAdicPairSupportExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (functions functionsOver)
open ProetaleAdicClosedPairSupport (boundary pairRestriction support inclusion)
open ProetaleAdicClosedPairEpi (sequence sequence_shortExact)
open ProetaleAdicBoundaryPairCoordinates (boundaryEquiv range_iff_diag)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} (L : Type) [Field L]
variable (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X)
variable [IsClosedImmersion i₀] [IsClosedImmersion i₁]
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁))

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))
private abbrev hS := sequence_shortExact i₀ i₁ ℓ hDisjoint

private def connecting : M ℓ × M ℓ →+ Sheaf.H (support i₀ i₁ ℓ) 1 :=
  ((hS L i₀ i₁ ℓ hDisjoint).extClass.postcomp integers (show 0 + 1 = 1 by rfl)).comp
    (boundaryEquiv L i₀ i₁ ℓ).symm.toAddMonoidHom

/-- The second-point value supplies the actual boundary injection. -/
def boundaryClass : M ℓ →+ Sheaf.H (support i₀ i₁ ℓ) 1 :=
  (connecting L i₀ i₁ ℓ hDisjoint).comp
    (AddMonoidHom.prod (0 : M ℓ →+ M ℓ) (AddMonoidHom.id (M ℓ)))

variable [PreconnectedSpace X]

private theorem connecting_zero_iff (a : M ℓ × M ℓ) :
    connecting L i₀ i₁ ℓ hDisjoint a = 0 ↔ a.1 = a.2 := by
  let e := boundaryEquiv L i₀ i₁ ℓ
  let c := integers (X := X)
  have h := Ext.covariant_sequence_exact₃' c (hS L i₀ i₁ ℓ hDisjoint) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  change ((hS L i₀ i₁ ℓ hDisjoint).extClass.postcomp c (show 0 + 1 = 1 by rfl)) (e.symm a) = 0 ↔ _
  rw [show ((hS L i₀ i₁ ℓ hDisjoint).extClass.postcomp c (show 0 + 1 = 1 by rfl)) (e.symm a) = 0 ↔
      e.symm a ∈ Set.range (Sheaf.H.map (pairRestriction i₀ i₁ ℓ) 0) from h (e.symm a)]
  constructor
  · rintro ⟨x, hx⟩
    exact (range_iff_diag L i₀ i₁ ℓ a).mp
      ⟨x, (congrArg e hx).trans (e.apply_symm_apply a)⟩
  · intro ha
    obtain ⟨x, hx⟩ := (range_iff_diag L i₀ i₁ ℓ a).mpr ha
    exact ⟨x, e.injective (hx.trans (e.apply_symm_apply a).symm)⟩

private theorem connecting_factor (a : M ℓ × M ℓ) :
    connecting L i₀ i₁ ℓ hDisjoint a = boundaryClass L i₀ i₁ ℓ hDisjoint (a.2 - a.1) := by
  let δ := connecting L i₀ i₁ ℓ hDisjoint
  have h : a = (a.1, a.1) + (0, a.2 - a.1) := by
    apply Prod.ext
    · exact (add_zero a.1).symm
    · change a.2 = a.1 + (a.2 - a.1)
      abel
  calc
    δ a = δ ((a.1, a.1) + (0, a.2 - a.1)) := congrArg δ h
    _ = δ (0, a.2 - a.1) := by
      rw [map_add, (connecting_zero_iff L i₀ i₁ ℓ hDisjoint (a.1, a.1)).mpr rfl, zero_add]
    _ = _ := rfl

theorem boundaryClass_injective : Function.Injective (boundaryClass L i₀ i₁ ℓ hDisjoint) := by
  intro a b hab
  apply sub_eq_zero.mp
  have hz : boundaryClass L i₀ i₁ ℓ hDisjoint (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact ((connecting_zero_iff L i₀ i₁ ℓ hDisjoint (0, a - b)).mp hz).symm

/-- The actual difference line is exactly the kernel of support cohomology to ambient cohomology. -/
theorem projection_exact :
    Function.Exact (boundaryClass L i₀ i₁ ℓ hDisjoint) (Sheaf.H.map (inclusion i₀ i₁ ℓ) 1) := by
  let e := boundaryEquiv L i₀ i₁ ℓ
  let c := integers (X := X)
  let δ₀ := (hS L i₀ i₁ ℓ hDisjoint).extClass.postcomp c (show 0 + 1 = 1 by rfl)
  let q := Sheaf.H.map (inclusion i₀ i₁ ℓ) 1
  have h := Ext.covariant_sequence_exact₁' c (hS L i₀ i₁ ℓ hDisjoint) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  have hExact : Function.Exact δ₀ q := h
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hExact x).mp hx
    let a := e y
    refine ⟨a.2 - a.1, (connecting_factor L i₀ i₁ ℓ hDisjoint a).symm.trans ?_⟩
    exact (congrArg δ₀ (e.symm_apply_apply y)).trans hy
  · rintro ⟨b, rfl⟩
    exact (hExact _).mpr ⟨e.symm (0, b), rfl⟩

variable [IsAlgClosed L]

private theorem point_HOne_subsingleton (i : Spec (CommRingCat.of L) ⟶ X) :
    Subsingleton (Sheaf.H (functionsOver (M ℓ) i) 1) := by
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton L
    (functions (M ℓ) (Spec (CommRingCat.of L))) 0
  exact ProetaleDirectImageHOne.directImage_HOne_subsingleton i _

private theorem boundary_HOne_subsingleton : Subsingleton (Sheaf.H (boundary i₀ i₁ ℓ) 1) := by
  let F := functionsOver (M ℓ) i₀
  let G := functionsOver (M ℓ) i₁
  letI := point_HOne_subsingleton L ℓ i₀
  letI := point_HOne_subsingleton L ℓ i₁
  let e := (cohomologyIso (X := X) (biprod.isoProd F G).symm 1).trans
    (Ext.addEquivBiprod (X := integers (X := X)) (Y₁ := F) (Y₂ := G) (n := 1))
  exact e.injective.subsingleton

include hDisjoint in
/-- The map from the true two-boundary support to ambient degree one is surjective. -/
theorem projection_surjective :
    Function.Surjective (Sheaf.H.map (inclusion i₀ i₁ ℓ) 1) := by
  let hZ := boundary_HOne_subsingleton L i₀ i₁ ℓ
  intro x
  exact Ext.covariant_sequence_exact₂ (integers (X := X)) (hS L i₀ i₁ ℓ hDisjoint) x (hZ.elim _ _)

end
end ManuscriptAudit.ProetaleAdicPairSupportExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicPairSupportExact.boundaryClass_injective,
      ``ManuscriptAudit.ProetaleAdicPairSupportExact.projection_exact,
      ``ManuscriptAudit.ProetaleAdicPairSupportExact.projection_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
