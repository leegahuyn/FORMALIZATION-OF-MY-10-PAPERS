import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KernelImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicBoundaryPairImageHZero
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicBoundaryPairCoordinates

/-! The actual two-point compact support kernel has one copy of the adic
integers in degree one when the preconnected ambient H¹ vanishes. -/

namespace ManuscriptAudit.ProetaleAdicBoundaryPairHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleAdicClosedPairSupport (boundary pairRestriction support)
open ProetaleAdicBoundaryPairImageHZero (imageHZeroEquiv)
open ProetaleAdicBoundaryPairCoordinates (boundaryEquiv range_iff_diag)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} [PreconnectedSpace X] (L : Type) [Field L]
variable (i₀ i₁ : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i₀] [IsClosedImmersion i₁]
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁))

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev F := functions (M ℓ) X
private abbrev d := pairRestriction i₀ i₁ ℓ
private abbrev S := KernelImageHOne.sequence (d i₀ i₁ ℓ)
private abbrev hS := KernelImageHOne.sequence_shortExact (d i₀ i₁ ℓ)
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private def coords : Sheaf.H (Abelian.image (d i₀ i₁ ℓ)) 0 ≃+ M ℓ × M ℓ :=
  (imageHZeroEquiv L i₀ i₁ ℓ hDisjoint).trans (boundaryEquiv L i₀ i₁ ℓ)

private def connecting : M ℓ × M ℓ →+ Sheaf.H (support i₀ i₁ ℓ) 1 :=
  ((hS i₀ i₁ ℓ).extClass.postcomp integers (show 0 + 1 = 1 by rfl)).comp
    (coords L i₀ i₁ ℓ hDisjoint).symm.toAddMonoidHom

set_option maxHeartbeats 2000000 in
private theorem coords_map (x : Sheaf.H (F (X := X) ℓ) 0) :
    coords L i₀ i₁ ℓ hDisjoint (Sheaf.H.map (S i₀ i₁ ℓ).g 0 x) =
      boundaryEquiv L i₀ i₁ ℓ (Sheaf.H.map (d i₀ i₁ ℓ) 0 x) := by
  change boundaryEquiv L i₀ i₁ ℓ (Sheaf.H.map (Abelian.image.ι (d i₀ i₁ ℓ)) 0
    (Sheaf.H.map (Abelian.factorThruImage (d i₀ i₁ ℓ)) 0 x)) = _
  rw [← Sheaf.H.map_comp_apply, Abelian.image.fac]

set_option maxHeartbeats 2100000 in
private theorem connecting_zero_iff (a : M ℓ × M ℓ) :
    connecting L i₀ i₁ ℓ hDisjoint a = 0 ↔ a.1 = a.2 := by
  let e := coords L i₀ i₁ ℓ hDisjoint
  let v := e.symm a
  have h := Ext.covariant_sequence_exact₃' integers (hS i₀ i₁ ℓ) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  change v.comp (hS i₀ i₁ ℓ).extClass (show 0 + 1 = 1 by rfl) = 0 ↔ _
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := (h v).mp hv
    apply (range_iff_diag L i₀ i₁ ℓ a).mp
    refine ⟨x, ?_⟩
    calc
      _ = e (Sheaf.H.map (S i₀ i₁ ℓ).g 0 x) := (coords_map L i₀ i₁ ℓ hDisjoint x).symm
      _ = e v := congrArg e hx
      _ = a := e.apply_symm_apply a
  · intro ha
    obtain ⟨x, hx⟩ := (range_iff_diag L i₀ i₁ ℓ a).mpr ha
    apply (h v).mpr
    refine ⟨x, e.injective ?_⟩
    change e (Sheaf.H.map (S i₀ i₁ ℓ).g 0 x) = e (e.symm a)
    exact (coords_map L i₀ i₁ ℓ hDisjoint x).trans (hx.trans (e.apply_symm_apply a).symm)

private theorem connecting_surjective (hAmbient : Subsingleton (Sheaf.H (F (X := X) ℓ) 1)) :
    Function.Surjective (connecting L i₀ i₁ ℓ hDisjoint) := by
  intro x
  let e := coords L i₀ i₁ ℓ hDisjoint
  have hx : Sheaf.H.map (S i₀ i₁ ℓ).f 1 x = 0 := hAmbient.elim _ _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ integers (hS i₀ i₁ ℓ) x hx
    (show 0 + 1 = 1 by rfl)
  refine ⟨e a, ?_⟩
  change (e.symm (e a)).comp (hS i₀ i₁ ℓ).extClass (show 0 + 1 = 1 by rfl) = x
  rw [e.symm_apply_apply]
  exact ha

/-- Native H¹ of the two-point kernel is the difference of its two actual boundary values. -/
def supportHOneEquiv (hAmbient : Subsingleton (Sheaf.H (F (X := X) ℓ) 1)) :
    Sheaf.H (support i₀ i₁ ℓ) 1 ≃+ M ℓ := by
  let δ := connecting L i₀ i₁ ℓ hDisjoint
  let emb : M ℓ →+ M ℓ × M ℓ :=
    { toFun := fun z ↦ (0, z)
      map_zero' := rfl
      map_add' := fun x y ↦ Prod.ext (zero_add 0).symm rfl }
  refine (AddEquiv.ofBijective (δ.comp emb) ⟨?_, ?_⟩).symm
  · intro a b hab
    apply sub_eq_zero.mp
    have h : δ (0, a - b) = 0 := by
      change (δ.comp emb) (a - b) = 0
      rw [map_sub, hab, sub_self]
    exact ((connecting_zero_iff L i₀ i₁ ℓ hDisjoint (0, a - b)).mp h).symm
  · intro x
    obtain ⟨a, ha⟩ := connecting_surjective L i₀ i₁ ℓ hDisjoint hAmbient x
    have hdiag : δ (a.1, a.1) = 0 :=
      (connecting_zero_iff L i₀ i₁ ℓ hDisjoint (a.1, a.1)).mpr rfl
    have hdecomp : a = (0, a.2 - a.1) + (a.1, a.1) := by
      apply Prod.ext
      · exact (zero_add a.1).symm
      · exact (sub_add_cancel a.2 a.1).symm
    refine ⟨a.2 - a.1, ?_⟩
    change δ (0, a.2 - a.1) = x
    rw [hdecomp, map_add, hdiag, add_zero] at ha
    exact ha

end

end ManuscriptAudit.ProetaleAdicBoundaryPairHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicBoundaryPairHOne.supportHOneEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
