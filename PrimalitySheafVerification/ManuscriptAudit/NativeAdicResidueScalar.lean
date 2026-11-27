import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicScalarAction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicReductionAllDegrees

/-! Actual scalar multiplication reduces to multiplication by the
residue coefficient in every native pro-étale cohomological degree. -/

namespace ManuscriptAudit.NativeAdicResidueScalar

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open NativeAdicScalarAction (scalarMap)
open ProetaleAdicHOneDetection (finiteCoefficient)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev J := Scheme.ProEt.topology X
private abbrev A := AddCommGrpCat.{1}

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
private abbrev rho (n : ℕ) :=
  (ProetaleCoefficientUniverseLift.lift X).map (ProetaleResidueSheaves.residueReduction X ℓ n)

private theorem nsmul_id_eval (F : Sheaf (J X) A) (m : ℕ) (U : X.ProEtᵒᵖ)
    (x : F.obj.obj U) : (m • 𝟙 F : F ⟶ F).hom.app U x = m • x := by
  let E := sheafToPresheaf (J X) A ⋙ (evaluation X.ProEtᵒᵖ A).obj U
  let Q := E.obj F
  change (E.map (m • 𝟙 F) : Q ⟶ Q) x = m • x
  rw [Functor.map_nsmul, E.map_id]
  rfl

private theorem H_map_nsmul_id (F : Sheaf (J X) A) (d m : ℕ) (x : Sheaf.H F d) :
    Sheaf.H.map (m • 𝟙 F) d x = m • x := by
  let h : (F ⟶ F) ≃+ Ext.{1} F F 0 := Ext.addEquiv₀.symm
  have hm : (Ext.mk₀ (m • 𝟙 F) : Ext.{1} F F 0) = m • Ext.mk₀ (𝟙 F) :=
    map_nsmul h m (𝟙 F)
  change x.comp (Ext.mk₀ (m • 𝟙 F)) (add_zero d) = m • x
  rw [hm]
  have hmul := map_nsmul (x.precomp F (add_zero d)) m (Ext.mk₀ (𝟙 F))
  change x.comp (m • Ext.mk₀ (𝟙 F)) (add_zero d) =
    m • x.comp (Ext.mk₀ (𝟙 F)) (add_zero d) at hmul
  rw [Ext.comp_mk₀_id] at hmul
  exact hmul

private theorem scalar_reduction (r : ℤ_[ℓ]) (n : ℕ) :
    scalarMap X ℓ r ≫ rho X ℓ n =
      rho X ℓ n ≫ ((PadicInt.toZModPow n r).val • 𝟙 (finiteCoefficient X ℓ n)) := by
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (show ℓ.Prime from Fact.out).ne_zero⟩
  let m := (PadicInt.toZModPow n r).val
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro x
  change (rho X ℓ n).hom.app U ((scalarMap X ℓ r).hom.app U x) =
    (m • 𝟙 (finiteCoefficient X ℓ n) : _ ⟶ _).hom.app U ((rho X ℓ n).hom.app U x)
  rw [nsmul_id_eval]
  apply ULift.ext
  apply ContinuousMap.ext
  intro a
  let f : C(U.unop.left, ℤ_[ℓ]) := x.down
  change PadicInt.toZModPow n (r * f a) =
    (m • (show C(U.unop.left, ZMod (ℓ ^ n)) from ((rho X ℓ n).hom.app U x).down)) a
  rw [ContinuousMap.nsmul_apply]
  change PadicInt.toZModPow n (r * f a) = m • PadicInt.toZModPow n (f a)
  rw [map_mul, nsmul_eq_mul]
  exact congrArg (fun b : ZMod (ℓ ^ n) ↦ b * PadicInt.toZModPow n (f a))
    (ZMod.natCast_zmod_val (PadicInt.toZModPow n r)).symm

/-- The residue of the actual scalar action is the corresponding ordinary additive multiple. -/
theorem reduction_scalar (d n : ℕ) (r : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ d) :
    Sheaf.H.map (rho X ℓ n) d (Sheaf.H.map (scalarMap X ℓ r) d x) =
      (PadicInt.toZModPow n r).val • Sheaf.H.map (rho X ℓ n) d x := by
  let f := scalarMap X ℓ r
  let g := rho X ℓ n
  let m := (PadicInt.toZModPow n r).val
  calc
    _ = Sheaf.H.map (f ≫ g) d x := (Sheaf.H.map_comp_apply f g x).symm
    _ = Sheaf.H.map (g ≫ (m • 𝟙 (finiteCoefficient X ℓ n))) d x :=
      congrArg (fun q ↦ Sheaf.H.map q d x) (scalar_reduction X ℓ r n)
    _ = Sheaf.H.map (m • 𝟙 (finiteCoefficient X ℓ n)) d (Sheaf.H.map g d x) :=
      Sheaf.H.map_comp_apply g _ x
    _ = _ := H_map_nsmul_id X (finiteCoefficient X ℓ n) d m (Sheaf.H.map g d x)

end
end ManuscriptAudit.NativeAdicResidueScalar

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAdicResidueScalar.reduction_scalar
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
